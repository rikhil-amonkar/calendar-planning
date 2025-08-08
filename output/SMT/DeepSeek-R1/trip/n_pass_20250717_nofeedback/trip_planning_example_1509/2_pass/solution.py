from z3 import *

def plan_activities(activities, resources, locations, max_time):
    s = Solver()
    
    # Activity variables
    start_vars = [Int(f'start_{i}') for i in range(len(activities))]
    end_vars = [Int(f'end_{i}') for i in range(len(activities))]
    location_vars = [Int(f'location_{i}') for i in range(len(activities))]
    
    # Basic activity constraints
    for i, act in enumerate(activities):
        # Duration constraint
        s.add(end_vars[i] == start_vars[i] + act['duration'])
        # Time bounds
        s.add(start_vars[i] >= 0)
        s.add(end_vars[i] <= max_time)
        # Location constraints
        allowed = act.get('allowed_locations', [loc['id'] for loc in locations])
        s.add(Or([location_vars[i] == loc_id for loc_id in allowed]))
    
    # Resource constraints
    for res in resources:
        capacity = res['capacity']
        res_id = res['id']
        time_points = range(0, max_time + 1)
        loc_ids = [loc['id'] for loc in locations]
        
        for t in time_points:
            for loc_id in loc_ids:
                total_demand = 0
                for i, act in enumerate(activities):
                    # Get resource demand if any
                    demand = 0
                    for r in act.get('resources', []):
                        if r['id'] == res_id:
                            demand = r['demand']
                            break
                    if demand == 0:
                        continue
                    
                    # Condition for activity demanding resource
                    cond = And(
                        start_vars[i] <= t,
                        t < end_vars[i],
                        location_vars[i] == loc_id
                    )
                    total_demand += If(cond, demand, 0)
                
                # Add capacity constraint
                s.add(total_demand <= capacity)
    
    # Dependency constraints
    for i, act in enumerate(activities):
        for dep_id in act.get('dependencies', []):
            # Find index of dependency
            for j, a in enumerate(activities):
                if a['id'] == dep_id:
                    s.add(start_vars[i] >= end_vars[j])
                    break
    
    # Makespan objective
    makespan = Int('makespan')
    s.add(makespan >= 0)
    for end in end_vars:
        s.add(makespan >= end)
    s.minimize(makespan)
    
    # Solve and return solution
    if s.check() == sat:
        model = s.model()
        solution = []
        for i, act in enumerate(activities):
            solution.append({
                'id': act['id'],
                'start': model.eval(start_vars[i]).as_long(),
                'end': model.eval(end_vars[i]).as_long(),
                'location': model.eval(location_vars[i]).as_long()
            })
        return solution
    else:
        return None  # No solution found