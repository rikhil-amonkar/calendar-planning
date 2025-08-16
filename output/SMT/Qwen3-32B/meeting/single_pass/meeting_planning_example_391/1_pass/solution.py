from z3 import *
import json

# Define the travel times between locations
travel_time = [
    [0, 17, 24, 16, 30],  # Sunset to [Alamo, Russian, Presidio, Financial]
    [16, 0, 13, 18, 17],  # Alamo
    [23, 15, 0, 14, 11],  # Russian Hill
    [15, 18, 14, 0, 23],  # Presidio
    [31, 17, 10, 22, 0]   # Financial District
]

# Create the solver
s = Optimize()

# Define friends variables for each step (0-3)
friends = [Int(f'friend_{i}') for i in range(4)]
start_times = [Int(f'start_{i}') for i in range(4)]
end_times = [Int(f'end_{i}') for i in range(4)]

# Define locations and times for each step (0-4)
locations = [Int(f'loc_{i}') for i in range(5)]
times = [Int(f'time_{i}') for i in range(5)]

# Initial location and time
s.add(locations[0] == 0)  # Sunset District
s.add(times[0] == 540)    # 9:00AM in minutes

for step in range(4):
    friend = friends[step]
    start = start_times[step]
    end = end_times[step]

    # Determine the friend's location based on friend variable
    loc_i = If(friend == 1, 1,
               If(friend == 2, 2,
                  If(friend == 3, 3,
                     If(friend == 4, 4, 0))))

    # Determine arrival time based on previous location and time
    arrival_time = times[step] + travel_time[locations[step]][loc_i]

    # Determine earliest_start, latest_start, duration
    earliest_start = If(friend == 1, 555,
                        If(friend == 2, 540,
                           If(friend == 3, 1110,
                              If(friend == 4, 1140, 0))))
    latest_start = If(friend == 1, 1215,
                      If(friend == 2, 720,
                         If(friend == 3, 1110,
                            If(friend == 4, 1260, 0))))
    duration = If(friend == 1, 75,
                  If(friend == 2, 30,
                     If(friend == 3, 45,
                        If(friend == 4, 45, 0))))

    # Add constraints for this step
    s.add(Implies(friend != 0, start >= arrival_time))
    s.add(Implies(friend != 0, start >= earliest_start))
    s.add(Implies(friend != 0, start <= latest_start))
    s.add(Implies(friend != 0, end == start + duration))

    # Compute new_loc and new_time for this step
    new_loc = If(friend != 0, loc_i, locations[step])
    new_time = If(friend != 0, end, times[step])

    # Set the next location and time
    s.add(locations[step+1] == new_loc)
    s.add(times[step+1] == new_time)

# Ensure each friend is included at most once
for i in range(4):
    for j in range(i+1, 4):
        s.add(Or(friends[i] == 0, friends[j] == 0, friends[i] != friends[j]))

# Maximize the number of friends included
num_friends = Sum([If(f != 0, 1, 0) for f in friends])
s.maximize(num_friends)

# Check if the problem is satisfiable
if s.check() == sat:
    model = s.model()
    # Extract the itinerary
    itinerary = []
    for step in range(4):
        f = model.eval(friends[step])
        if f != 0:
            start = model.eval(start_times[step])
            end = model.eval(end_times[step])
            # Map friend number to name
            if f == 1:
                person = "Kevin"
            elif f == 2:
                person = "Kimberly"
            elif f == 3:
                person = "Joseph"
            elif f == 4:
                person = "Thomas"
            else:
                continue  # should not happen
            # Convert start and end times to HH:MM format
            def to_time_str(minutes):
                hours = minutes // 60
                mins = minutes % 60
                return f"{hours:02d}:{mins:02d}"
            itinerary.append({
                "action": "meet",
                "person": person,
                "start_time": to_time_str(start),
                "end_time": to_time_str(end)
            })
    # Output the JSON
    print("SOLUTION:")
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print("No solution found.")