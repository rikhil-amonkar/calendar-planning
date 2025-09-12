import z3
import json

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def main():
    # Define friends and their parameters
    friends = [
        {'name': 'Sarah', 'location': 'Sunset District', 'available_start': 645, 'available_end': 1020, 'min_duration': 30},
        {'name': 'Richard', 'location': 'Haight-Ashbury', 'available_start': 705, 'available_end': 945, 'min_duration': 90},
        {'name': 'Elizabeth', 'location': 'Mission District', 'available_start': 660, 'available_end': 1035, 'min_duration': 120},
        {'name': 'Michelle', 'location': 'Golden Gate Park', 'available_start': 1095, 'available_end': 1245, 'min_duration': 90},
    ]
    
    # Define location names and mapping
    location_names = ['Richmond District', 'Sunset District', 'Haight-Ashbury', 'Mission District', 'Golden Gate Park']
    
    # Z3 solver setup
    s = z3.Optimize()
    
    # Variables for time and location at each step (0-4)
    time_vars = [z3.Int(f'time_{i}') for i in range(5)]
    location_vars = [z3.Int(f'location_{i}') for i in range(5)]
    
    # Initial constraints
    s.add(time_vars[0] == 540)  # 9:00 AM in minutes
    s.add(location_vars[0] == 0)  # Richmond District is index 0
    
    # Variables for each step (used, friend, start, end)
    used = [z3.Bool(f'used_{i}') for i in range(4)]
    friend = [z3.Int(f'friend_{i}') for i in range(4)]
    start = [z3.Int(f'start_{i}') for i in range(4)]
    end = [z3.Int(f'end_{i}') for i in range(4)]
    
    # Add constraints for each step
    for i in range(4):
        # Friend must be between 0 and 3 if used
        s.add(z3.Implies(used[i], z3.And(friend[i] >= 0, friend[i] <= 3)))
        
        # Ensure friends are unique if used
        for j in range(i):
            s.add(z3.Implies(z3.And(used[i], used[j]), friend[i] != friend[j]))
    
    for i in range(4):
        # Previous time and location
        prev_time = time_vars[i]
        prev_loc = location_vars[i]
        curr_friend = friend[i]
        curr_used = used[i]
        
        # Define friend parameters based on friend[i]
        # available_start
        available_start = z3.If(curr_friend == 0, 645,
                                z3.If(curr_friend == 1, 705,
                                      z3.If(curr_friend == 2, 660,
                                            z3.If(curr_friend == 3, 1095, 0))))
        # available_end
        available_end = z3.If(curr_friend == 0, 1020,
                              z3.If(curr_friend == 1, 945,
                                    z3.If(curr_friend == 2, 1035,
                                          z3.If(curr_friend == 3, 1245, 0))))
        # min_duration
        min_duration = z3.If(curr_friend == 0, 30,
                             z3.If(curr_friend == 1, 90,
                                   z3.If(curr_friend == 2, 120,
                                         z3.If(curr_friend == 3, 90, 0))))
        # friend_loc
        friend_loc = z3.If(curr_friend == 0, 1,
                           z3.If(curr_friend == 1, 2,
                                 z3.If(curr_friend == 2, 3,
                                       z3.If(curr_friend == 3, 4, 0))))
        
        # Travel time from previous location to friend's location
        travel_time = z3.If(prev_loc == 0,  # Richmond
                            z3.If(friend_loc == 0, 0,
                                  z3.If(friend_loc == 1, 11,
                                        z3.If(friend_loc == 2, 10,
                                              z3.If(friend_loc == 3, 20,
                                                    z3.If(friend_loc == 4, 9, 0)))),
                            z3.If(prev_loc == 1,  # Sunset
                                  z3.If(friend_loc == 0, 12,
                                        z3.If(friend_loc == 1, 0,
                                              z3.If(friend_loc == 2, 15,
                                                    z3.If(friend_loc == 3, 24,
                                                          z3.If(friend_loc == 4, 11, 0)))),
                                  z3.If(prev_loc == 2,  # Haight
                                        z3.If(friend_loc == 0, 10,
                                              z3.If(friend_loc == 1, 15,
                                                    z3.If(friend_loc == 2, 0,
                                                          z3.If(friend_loc == 3, 11,
                                                                z3.If(friend_loc == 4, 7, 0)))),
                                        z3.If(prev_loc == 3,  # Mission
                                              z3.If(friend_loc == 0, 20,
                                                    z3.If(friend_loc == 1, 24,
                                                          z3.If(friend_loc == 2, 12,
                                                                z3.If(friend_loc == 3, 0,
                                                                      z3.If(friend_loc == 4, 17, 0)))),
                                              z3.If(prev_loc == 4,  # Golden Gate
                                                    z3.If(friend_loc == 0, 7,
                                                          z3.If(friend_loc == 1, 10,
                                                                z3.If(friend_loc == 2, 7,
                                                                      z3.If(friend_loc == 3, 17,
                                                                            z3.If(friend_loc == 4, 0, 0)))),
                                                    0))))
        
        # arrival is prev_time + travel_time
        arrival = prev_time + travel_time
        
        # Constraints if used
        s.add(z3.Implies(curr_used, start[i] >= arrival))
        s.add(z3.Implies(curr_used, start[i] >= available_start))
        s.add(z3.Implies(curr_used, end[i] == start[i] + min_duration))
        s.add(z3.Implies(curr_used, end[i] <= available_end))
        
        # Update time and location for next step
        next_time = time_vars[i+1]
        next_loc = location_vars[i+1]
        
        s.add(z3.Implies(curr_used, next_time == end[i]))
        s.add(z3.Implies(z3.Not(curr_used), next_time == prev_time))
        
        s.add(z3.Implies(curr_used, next_loc == friend_loc))
        s.add(z3.Implies(z3.Not(curr_used), next_loc == prev_loc))
    
    # Maximize the number of friends met
    s.maximize(z3.Sum([z3.If(used[i], 1, 0) for i in range(4)]))
    
    # Check if solution exists
    if s.check() == z3.sat:
        model = s.model()
        
        # Build itinerary
        itinerary = []
        for i in range(4):
            if model.eval(used[i]).as_string() == 'True':
                friend_index = model.eval(friend[i]).as_long()
                start_time = model.eval(start[i]).as_long()
                end_time = model.eval(end[i]).as_long()
                person = friends[friend_index]['name']
                location = friends[friend_index]['location']
                itinerary.append({
                    "action": "meet",
                    "location": location,
                    "person": person,
                    "start_time": minutes_to_time(start_time),
                    "end_time": minutes_to_time(end_time)
                })
        # Output as JSON
        print(json.dumps({"itinerary": itinerary}, indent=2))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()