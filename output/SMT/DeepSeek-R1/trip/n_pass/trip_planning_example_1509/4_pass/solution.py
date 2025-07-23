from z3 import *

def plan_activities(activities, resources, locations, max_time):
    s = Solver()
    
    # Extract location IDs
    location_ids = [loc['id'] for loc in locations]
    
    # Activity variables
    start_vars = [Int(f'start_{i}') for i in range(len(activities))]
    end_vars = [Int(f'end_{i}') for i in range(len(activities))]
    location_vars = [Int(f'location_{i}') for i in range(len(activities))]
    
    # Makespan variable
    makespan = Int('makespan')
    s.add(makespan >= 0)
    s.add(makespan <= max_time)
    
    # Basic activity constraints
    for i, act in enumerate(activities):
        # Duration constraint
        s.add(end_vars[i] == start_vars[i] + act['duration'])
        # Time bounds
        s.add(start_vars[i] >= 0)
        s.add(end_vars[i] <= makespan)  # Use makespan instead of max_time
        
        # Location constraints
        allowed_locations = act.get('allowed_locations', location_ids)
        s.add(Or([location_vars[i] == loc_id for loc_id in allowed_locations]))
    
    # Resource constraints
    for res in resources:
        res_id = res['id']
        capacity = res['capacity']
        
        # Precompute resource demands
        res_demands = []
        for i, act in enumerate(activities):
            demand_val = 0
            for r in act.get('resources', []):
                if r['id'] == res_id:
                    demand_val = r['demand']
                    break
            res_demands.append(demand_val)
        
        # Consider only time points where activities start/end
        time_points = []
        for i in range(len(activities)):
            time_points.append(start_vars[i])
            time_points.append(end_vars[i])
        
        # Check resource usage at critical time points
        for loc_id in location_ids:
            for t in time_points:
                total_demand = Sum([
                    If(And(
                        start_vars[i] <= t, 
                        t < end_vars[i],
                        location_vars[i] == loc_id,
                        res_demands[i] > 0
                    ), res_demands[i], 0)
                    for i in range(len(activities))
                ])
                s.add(total_demand <= capacity)
    
    # Dependency constraints
    for i, act in enumerate(activities):
        deps = act.get('dependencies', [])
        for dep_id in deps:
            dep_index = None
            for j, a in enumerate(activities):
                if a['id'] == dep_id:
                    dep_index = j
                    break
            if dep_index is not None:
                s.add(start_vars[i] >= end_vars[dep_index])
    
    # Minimize makespan
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