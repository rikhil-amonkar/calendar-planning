from z3 import *

# Define the locations and their corresponding indices
locations = ["Financial District", "Golden Gate Park", "Chinatown", "Union Square", 
             "Fisherman's Wharf", "Pacific Heights", "North Beach"]
location_indices = {loc: i for i, loc in enumerate(locations)}

# Travel times matrix
travel_times = [
    [0, 23, 5, 9, 10, 13, 7],
    [26, 0, 23, 22, 24, 16, 24],
    [5, 23, 0, 7, 8, 10, 3],
    [9, 22, 7, 0, 15, 15, 10],
    [11, 25, 12, 13, 0, 12, 6],
    [13, 15, 11, 12, 13, 0, 9],
    [8, 22, 6, 7, 5, 8, 0]
]

# Availability windows and required meeting durations
availabilities = {
    "Stephanie": ("Golden Gate Park", 11*60, 15*60, 105),  # 11:00AM to 3:00PM, 105 minutes
    "Karen": ("Chinatown", 1*45+12*60, 4*30+12*60, 15),  # 1:45PM to 4:30PM, 15 minutes
    "Brian": ("Union Square", 3*60, 5*15+12*60, 30),  # 3:00PM to 5:15PM, 30 minutes
    "Rebecca": ("Fisherman's Wharf", 8*60, 11*15, 30),  # 8:00AM to 11:15AM, 30 minutes
    "Joseph": ("Pacific Heights", 8*15+12*60, 9*30+12*60, 60),  # 8:15AM to 9:30AM, 60 minutes
    "Steven": ("North Beach", 2*30+12*60, 8*45+12*60, 120)  # 2:30PM to 8:45PM, 120 minutes
}

# Create a solver instance
solver = Solver()

# Variables for start times of each meeting
start_times = {name: Int(name + "_start") for name in availabilities}

# Constraints for each meeting
for name, (location, start, end, duration) in availabilities.items():
    solver.add(start_times[name] >= start)
    solver.add(start_times[name] <= end - duration)

# Travel time constraints
current_location = "Financial District"
current_time = 9 * 60  # 9:00AM

# List to store the order of meetings
meeting_order = []

# Add constraints to ensure we visit exactly 5 friends
selected_meetings = BoolVector('selected', len(availabilities))

# Ensure exactly 5 meetings are selected
solver.add(Sum([If(selected_meetings[i], 1, 0) for i in range(len(availabilities))]) == 5)

# Add constraints for selected meetings
for i, (name, (location, start, end, duration)) in enumerate(availabilities.items()):
    location_index = location_indices[location]
    current_location_index = location_indices[current_location]
    
    # Ensure we have enough time to travel to the next location if selected
    solver.add(Implies(selected_meetings[i], start_times[name] >= current_time + travel_times[current_location_index][location_index]))
    
    # Update current location and time after meeting if selected
    current_location = location
    current_time = start_times[name] + duration
    
    # Add to meeting order
    meeting_order.append(name)

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    print("SOLUTION:")
    selected_names = [name for i, name in enumerate(availabilities) if model.evaluate(selected_meetings[i])]
    selected_start_times = {name: model[start_times[name]].as_long() for name in selected_names}
    
    for name in selected_names:
        start_time = selected_start_times[name]
        hours = start_time // 60
        minutes = start_time % 60
        print(f"Meet {name} at {hours:02}:{minutes:02}")
else:
    print("No solution found")