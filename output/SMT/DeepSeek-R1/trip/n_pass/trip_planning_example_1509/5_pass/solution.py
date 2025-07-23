from z3 import *

def plan_activities(activities, resources, locations, max_time):
    s = Solver()
    
    # Extract location IDs
    location_ids = [loc['id'] for loc in locations]
    
    # Create activity variables
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
        s.add(end_vars[i] <= max_time)
        # Location constraints
        allowed = act.get('allowed_locations', location_ids)
        s.add(Or([location_vars[i] == loc_id for loc_id in allowed]))
    
    # Precompute resource demands
    resource_demands = {}
    for res in resources:
        res_id = res['id']
        demands = []
        for act in activities:
            d = 0
            for r in act.get('resources', []):
                if r['id'] == res_id:
                    d = r['demand']
                    break
            demands.append(d)
        resource_demands[res_id] = demands
    
    # Resource constraints using critical time points
    for res in resources:
        res_id = res['id']
        capacity = res['capacity']
        demands = resource_demands[res_id]
        
        # Get all start and end times
        time_points = list(set(start_vars + end_vars))
        
        for loc_id in location_ids:
            for t in time_points:
                total_demand = 0
                for i, act in enumerate(activities):
                    # Skip activities that don't use this resource
                    if demands[i] == 0:
                        continue
                    
                    # Condition for activity being active at time t at location loc_id
                    cond = And(
                        start_vars[i] <= t,
                        t < end_vars[i],
                        location_vars[i] == loc_id
                    )
                    total_demand += If(cond, demands[i], 0)
                
                # Add resource capacity constraint
                s.add(total_demand <= capacity)
    
    # Dependency constraints
    for i, act in enumerate(activities):
        for dep_id in act.get('dependencies', []):
            # Find dependency index
            dep_index = next((j for j, a in enumerate(activities) if a['id'] == dep_id), None)
            if dep_index is not None:
                s.add(start_vars[i] >= end_vars[dep_index])
    
    # Makespan constraints
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