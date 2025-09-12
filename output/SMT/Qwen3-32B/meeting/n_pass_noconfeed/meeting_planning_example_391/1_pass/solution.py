import z3
import json

# Define friends' data
friends = [
    {
        'name': 'Kevin',
        'location': 1,  # Alamo Square
        'available_start': 495,
        'available_end': 1110,
        'min_duration': 75
    },
    {
        'name': 'Kimberly',
        'location': 2,  # Russian Hill
        'available_start': 525,
        'available_end': 750,
        'min_duration': 30
    },
    {
        'name': 'Joseph',
        'location': 3,  # Presidio
        'available_start': 1110,
        'available_end': 1155,
        'min_duration': 45
    },
    {
        'name': 'Thomas',
        'location': 4,  # Financial District
        'available_start': 1140,
        'available_end': 1425,
        'min_duration': 45
    }
]

# Define travel times between locations
travel_time = [
    [0, 17, 24, 16, 30],  # from Sunset (0)
    [16, 0, 13, 18, 17],   # from Alamo Square (1)
    [23, 15, 0, 14, 11],   # from Russian Hill (2)
    [15, 18, 14, 0, 23],   # from Presidio (3)
    [31, 17, 10, 22, 0]    # from Financial District (4)
]

# Helper function to get travel time between locations
def get_travel_time(prev_loc, current_loc):
    return z3.If(prev_loc == 0,
                 z3.If(current_loc == 1, 17,
                       z3.If(current_loc == 2, 24,
                             z3.If(current_loc == 3, 16, 30))),
                 z3.If(prev_loc == 1,
                       z3.If(current_loc == 0, 16,
                             z3.If(current_loc == 2, 13,
                                   z3.If(current_loc == 3, 18, 17))),
                       z3.If(prev_loc == 2,
                             z3.If(current_loc == 0, 23,
                                   z3.If(current_loc == 1, 15,
                                         z3.If(current_loc == 3, 14, 11))),
                             z3.If(prev_loc == 3,
                                   z3.If(current_loc == 0, 15,
                                         z3.If(current_loc == 1, 18,
                                               z3.If(current_loc == 2, 14, 23))),
                                   z3.If(prev_loc == 4,
                                         z3.If(current_loc == 0, 31,
                                               z3.If(current_loc == 1, 17,
                                                     z3.If(current_loc == 2, 10, 22))),
                                         0)))))

# Location names for output
location_names = ["Sunset District", "Alamo Square", "Russian Hill", "Presidio", "Financial District"]

# Create Z3 solver with optimization
opt = z3.Optimize()

# Create variables for each of the 4 possible meeting positions
used = [z3.Bool(f'used_{i}') for i in range(4)]
friend = [z3.Int(f'friend_{i}') for i in range(4)]
start = [z3.Int(f'start_{i}') for i in range(4)]
end = [z3.Int(f'end_{i}') for i in range(4)]

# Constraint: each friend can be used at most once
for i in range(4):
    for j in range(i+1, 4):
        opt.add(z3.Implies(z3.And(used[i], used[j]), friend[i] != friend[j]))

# Constraint: friend indices must be in range if used
for i in range(4):
    opt.add(z3.Implies(used[i], z3.And(friend[i] >= 0, friend[i] <= 3)))

# Process each meeting position
for i in range(4):
    # Define expressions for current position
    loc_i = z3.If(friend[i] == 0, 1,
                  z3.If(friend[i] == 1, 2,
                        z3.If(friend[i] == 2, 3, 4)))
    
    available_start_i = z3.If(friend[i] == 0, 495,
                              z3.If(friend[i] == 1, 525,
                                    z3.If(friend[i] == 2, 1110, 1140)))
    
    available_end_i = z3.If(friend[i] == 0, 1110,
                            z3.If(friend[i] == 1, 750,
                                  z3.If(friend[i] == 2, 1155, 1425)))
    
    min_duration_i = z3.If(friend[i] == 0, 75,
                           z3.If(friend[i] == 1, 30,
                                 z3.If(friend[i] == 2, 45, 45)))
    
    # Determine previous end and location based on previous positions
    if i == 0:
        prev_end = 540  # Initial arrival time at Sunset District
        prev_loc = 0
    else:
        # Build expressions for previous end and location
        prev_end = z3.If(used[i-1], end[i-1], 
                         z3.If(i >= 2, z3.If(used[i-2], end[i-2], 
                                            z3.If(i >= 3, z3.If(used[i-3], end[i-3], 540), 540)), 540))
        
        prev_loc = z3.If(used[i-1], 
                         z3.If(friend[i-1] == 0, 1,
                               z3.If(friend[i-1] == 1, 2,
                                     z3.If(friend[i-1] == 2, 3, 4))),
                         z3.If(i >= 2, z3.If(used[i-2], 
                                             z3.If(friend[i-2] == 0, 1,
                                                   z3.If(friend[i-2] == 1, 2,
                                                         z3.If(friend[i-2] == 2, 3, 4))),
                                             z3.If(i >= 3, z3.If(used[i-3], 
                                                                 z3.If(friend[i-3] == 0, 1,
                                                                       z3.If(friend[i-3] == 1, 2,
                                                                             z3.If(friend[i-3] == 2, 3, 4))),
                                                                 0), 0)), 0))
    
    # Calculate travel time for current position
    travel_time_i = get_travel_time(prev_loc, loc_i)
    
    # Add constraints for current position
    opt.add(z3.Implies(used[i], start[i] >= prev_end + travel_time_i))
    opt.add(z3.Implies(used[i], start[i] >= available_start_i))
    opt.add(z3.Implies(used[i], end[i] == start[i] + min_duration_i))
    opt.add(z3.Implies(used[i], end[i] <= available_end_i))

# Add objective to maximize number of friends met
opt.maximize(z3.Sum([z3.If(u, 1, 0) for u in used]))

# Check for solution
if opt.check() == z3.sat:
    model = opt.model()
    itinerary = []
    for i in range(4):
        if model.evaluate(used[i]):
            f_idx = model.evaluate(friend[i]).as_long()
            f_name = friends[f_idx]['name']
            loc_idx = friends[f_idx]['location']
            s = model.evaluate(start[i]).as_long()
            e = model.evaluate(end[i]).as_long()
            
            # Convert minutes to H:MM format
            def to_time(m):
                h = m // 60
                mm = m % 60
                return f"{h}:{mm:02d}"
            
            itinerary.append({
                "action": "meet",
                "location": location_names[loc_idx],
                "person": f_name,
                "start_time": to_time(s),
                "end_time": to_time(e)
            })
    
    # Sort by start time
    itinerary.sort(key=lambda x: x['start_time'])
    
    # Output JSON
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print("No solution found.")