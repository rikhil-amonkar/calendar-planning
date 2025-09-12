import json
from z3 import *

# Define friends and their parameters
friends = [
    {'name': 'Richard', 'location': 3, 'available_start': 435, 'available_end': 615, 'min_duration': 75},
    {'name': 'Stephanie', 'location': 1, 'available_start': 495, 'available_end': 825, 'min_duration': 90},
    {'name': 'Sandra', 'location': 2, 'available_start': 780, 'available_end': 1170, 'min_duration': 15},
    {'name': 'Brian', 'location': 4, 'available_start': 735, 'available_end': 960, 'min_duration': 120},
    {'name': 'Jason', 'location': 5, 'available_start': 510, 'available_end': 1065, 'min_duration': 60}
]

# Define travel times between locations (0: Haight-Ashbury, ..., 5: Fisherman's Wharf)
travel_time = [
    [0, 11, 18, 12, 17, 23],  # Haight-Ashbury (0)
    [12, 0, 15, 16, 15, 22],  # Mission (1)
    [19, 13, 0, 23, 23, 25],  # Bayview (2)
    [11, 15, 22, 0, 7, 13],   # Pacific Heights (3)
    [17, 16, 23, 7, 0, 7],    # Russian Hill (4)
    [22, 22, 26, 12, 7, 0]    # Fisherman's Wharf (5)
]

MAX_STEPS = 5  # Maximum number of friends to meet

# Create the Z3 solver
s = Optimize()

# Variables for each step
friend_ids = []
start_times = []
end_times = []

prev_loc = 0  # Starting location (Haight-Ashbury)
prev_time = 540  # Starting time (9:00 AM in minutes since midnight)

for step in range(MAX_STEPS):
    # Create variables for this step
    friend_id = Int(f'friend_id_{step}')
    start_time = Int(f'start_time_{step}')
    end_time = Int(f'end_time_{step}')
    
    friend_ids.append(friend_id)
    start_times.append(start_time)
    end_times.append(end_time)
    
    # Add constraint: friend_id is between 0 and 5 (0 means no meeting)
    s.add(And(friend_id >= 0, friend_id <= 5))
    
    # Determine current location based on friend_id
    current_loc = If(friend_id != 0, friends[friend_id - 1]['location'], prev_loc)
    
    # Compute travel time for this step
    travel_time_step = If(prev_loc == 0,
        If(current_loc == 0, 0,
            If(current_loc == 1, 11,
                If(current_loc == 2, 18,
                    If(current_loc == 3, 12,
                        If(current_loc == 4, 17,
                            If(current_loc == 5, 23, 0))))),
        If(prev_loc == 1,
            If(current_loc == 0, 12,
                If(current_loc == 1, 0,
                    If(current_loc == 2, 15,
                        If(current_loc == 3, 16,
                            If(current_loc == 4, 15,
                                If(current_loc == 5, 22, 0)))))), 
            If(prev_loc == 2,
                If(current_loc == 0, 19,
                    If(current_loc == 1, 13,
                        If(current_loc == 2, 0,
                            If(current_loc == 3, 23,
                                If(current_loc == 4, 23,
                                    If(current_loc == 5, 25, 0)))))), 
                If(prev_loc == 3,
                    If(current_loc == 0, 11,
                        If(current_loc == 1, 15,
                            If(current_loc == 2, 22,
                                If(current_loc == 3, 0,
                                    If(current_loc == 4, 7,
                                        If(current_loc == 5, 13, 0)))))), 
                    If(prev_loc == 4,
                        If(current_loc == 0, 17,
                            If(current_loc == 1, 16,
                                If(current_loc == 2, 23,
                                    If(current_loc == 3, 7,
                                        If(current_loc == 4, 0,
                                            If(current_loc == 5, 7, 0)))))), 
                        If(prev_loc == 5,
                            If(current_loc == 0, 22,
                                If(current_loc == 1, 22,
                                    If(current_loc == 2, 26,
                                        If(current_loc == 3, 12,
                                            If(current_loc == 4, 7,
                                                If(current_loc == 5, 0, 0))))),
                            0))))) 
    
    arrival_time = prev_time + travel_time_step
    
    # Determine friend's available_start, available_end, and min_duration based on friend_id
    available_start_expr = If(friend_id == 1, friends[0]['available_start'],
        If(friend_id == 2, friends[1]['available_start'],
            If(friend_id == 3, friends[2]['available_start'],
                If(friend_id == 4, friends[3]['available_start'],
                    If(friend_id == 5, friends[4]['available_start'], 0))))
    )
    
    available_end_expr = If(friend_id == 1, friends[0]['available_end'],
        If(friend_id == 2, friends[1]['available_end'],
            If(friend_id == 3, friends[2]['available_end'],
                If(friend_id == 4, friends[3]['available_end'],
                    If(friend_id == 5, friends[4]['available_end'], 0))))
    )
    
    min_duration_expr = If(friend_id == 1, friends[0]['min_duration'],
        If(friend_id == 2, friends[1]['min_duration'],
            If(friend_id == 3, friends[2]['min_duration'],
                If(friend_id == 4, friends[3]['min_duration'],
                    If(friend_id == 5, friends[4]['min_duration'], 0))))
    )
    
    # Add constraints for this step if friend_id is not zero
    s.add(Implies(friend_id != 0, start_time >= arrival_time))
    s.add(Implies(friend_id != 0, start_time >= available_start_expr))
    s.add(Implies(friend_id != 0, start_time <= available_end_expr))
    s.add(Implies(friend_id != 0, end_time == start_time + min_duration_expr))
    s.add(Implies(friend_id != 0, end_time <= available_end_expr))
    
    # Update prev_loc and prev_time for the next step
    prev_loc = If(friend_id != 0, current_loc, prev_loc)
    prev_time = If(friend_id != 0, end_time, prev_time)

# Add constraints that each friend is scheduled at most once
for i in range(MAX_STEPS):
    for j in range(i + 1, MAX_STEPS):
        # If both steps i and j have non-zero friend_ids, they must be different
        s.add(Or(friend_ids[i] == 0, friend_ids[j] == 0, friend_ids[i] != friend_ids[j]))

# Maximize the number of meetings
count = Sum([If(fid != 0, 1, 0) for fid in friend_ids])
s.maximize(count)

# Check if a solution exists
if s.check() == sat:
    model = s.model()
    
    # Extract the itinerary
    itinerary = []
    for step in range(MAX_STEPS):
        fid = model.eval(friend_ids[step])
        if fid != 0:
            # Get friend's name
            friend_idx = fid - 1
            name = friends[friend_idx]['name']
            # Get start and end times in minutes
            st = model.eval(start_times[step])
            et = model.eval(end_times[step])
            # Convert to H:MM format
            def to_time_str(m):
                hours = m // 60
                minutes = m % 60
                return f"{hours}:{minutes:02d}"
            start_time_str = to_time_str(st)
            end_time_str = to_time_str(et)
            itinerary.append({
                "action": "meet",
                "location": "Location Name",  # Placeholder
                "person": name,
                "start_time": start_time_str,
                "end_time": end_time_str
            })
    
    # Replace "Location Name" with actual names
    location_names = {
        0: "Haight-Ashbury",
        1: "Mission District",
        2: "Bayview",
        3: "Pacific Heights",
        4: "Russian Hill",
        5: "Fisherman's Wharf"
    }
    for item in itinerary:
        friend = next(f for f in friends if f['name'] == item['person'])
        item['location'] = location_names[friend['location']]
    
    # Output as JSON
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print("No solution found.")