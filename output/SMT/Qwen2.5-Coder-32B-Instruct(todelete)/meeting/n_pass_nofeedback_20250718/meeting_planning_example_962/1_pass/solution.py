from z3 import *

# Define the locations and their travel times
locations = [
    "The Castro", "Marina District", "Presidio", "North Beach", "Embarcadero",
    "Haight-Ashbury", "Golden Gate Park", "Richmond District", "Alamo Square",
    "Financial District", "Sunset District"
]

travel_times = {
    ("The Castro", "Marina District"): 21,
    ("The Castro", "Presidio"): 20,
    ("The Castro", "North Beach"): 20,
    ("The Castro", "Embarcadero"): 22,
    ("The Castro", "Haight-Ashbury"): 6,
    ("The Castro", "Golden Gate Park"): 11,
    ("The Castro", "Richmond District"): 16,
    ("The Castro", "Alamo Square"): 8,
    ("The Castro", "Financial District"): 21,
    ("The Castro", "Sunset District"): 17,
    ("Marina District", "The Castro"): 22,
    ("Marina District", "Presidio"): 10,
    ("Marina District", "North Beach"): 11,
    ("Marina District", "Embarcadero"): 14,
    ("Marina District", "Haight-Ashbury"): 16,
    ("Marina District", "Golden Gate Park"): 18,
    ("Marina District", "Richmond District"): 11,
    ("Marina District", "Alamo Square"): 15,
    ("Marina District", "Financial District"): 17,
    ("Marina District", "Sunset District"): 19,
    ("Presidio", "The Castro"): 21,
    ("Presidio", "Marina District"): 11,
    ("Presidio", "North Beach"): 18,
    ("Presidio", "Embarcadero"): 20,
    ("Presidio", "Haight-Ashbury"): 15,
    ("Presidio", "Golden Gate Park"): 12,
    ("Presidio", "Richmond District"): 7,
    ("Presidio", "Alamo Square"): 19,
    ("Presidio", "Financial District"): 23,
    ("Presidio", "Sunset District"): 15,
    ("North Beach", "The Castro"): 23,
    ("North Beach", "Marina District"): 9,
    ("North Beach", "Presidio"): 17,
    ("North Beach", "Embarcadero"): 6,
    ("North Beach", "Haight-Ashbury"): 18,
    ("North Beach", "Golden Gate Park"): 22,
    ("North Beach", "Richmond District"): 18,
    ("North Beach", "Alamo Square"): 16,
    ("North Beach", "Financial District"): 8,
    ("North Beach", "Sunset District"): 27,
    ("Embarcadero", "The Castro"): 25,
    ("Embarcadero", "Marina District"): 12,
    ("Embarcadero", "Presidio"): 20,
    ("Embarcadero", "North Beach"): 5,
    ("Embarcadero", "Haight-Ashbury"): 21,
    ("Embarcadero", "Golden Gate Park"): 25,
    ("Embarcadero", "Richmond District"): 21,
    ("Embarcadero", "Alamo Square"): 19,
    ("Embarcadero", "Financial District"): 5,
    ("Embarcadero", "Sunset District"): 30,
    ("Haight-Ashbury", "The Castro"): 6,
    ("Haight-Ashbury", "Marina District"): 17,
    ("Haight-Ashbury", "Presidio"): 15,
    ("Haight-Ashbury", "North Beach"): 19,
    ("Haight-Ashbury", "Embarcadero"): 20,
    ("Haight-Ashbury", "Golden Gate Park"): 7,
    ("Haight-Ashbury", "Richmond District"): 10,
    ("Haight-Ashbury", "Alamo Square"): 5,
    ("Haight-Ashbury", "Financial District"): 21,
    ("Haight-Ashbury", "Sunset District"): 15,
    ("Golden Gate Park", "The Castro"): 13,
    ("Golden Gate Park", "Marina District"): 16,
    ("Golden Gate Park", "Presidio"): 11,
    ("Golden Gate Park", "North Beach"): 23,
    ("Golden Gate Park", "Embarcadero"): 25,
    ("Golden Gate Park", "Haight-Ashbury"): 7,
    ("Golden Gate Park", "Richmond District"): 7,
    ("Golden Gate Park", "Alamo Square"): 9,
    ("Golden Gate Park", "Financial District"): 26,
    ("Golden Gate Park", "Sunset District"): 10,
    ("Richmond District", "The Castro"): 16,
    ("Richmond District", "Marina District"): 9,
    ("Richmond District", "Presidio"): 7,
    ("Richmond District", "North Beach"): 17,
    ("Richmond District", "Embarcadero"): 19,
    ("Richmond District", "Haight-Ashbury"): 10,
    ("Richmond District", "Golden Gate Park"): 9,
    ("Richmond District", "Alamo Square"): 13,
    ("Richmond District", "Financial District"): 22,
    ("Richmond District", "Sunset District"): 11,
    ("Alamo Square", "The Castro"): 8,
    ("Alamo Square", "Marina District"): 15,
    ("Alamo Square", "Presidio"): 17,
    ("Alamo Square", "North Beach"): 15,
    ("Alamo Square", "Embarcadero"): 16,
    ("Alamo Square", "Haight-Ashbury"): 5,
    ("Alamo Square", "Golden Gate Park"): 9,
    ("Alamo Square", "Richmond District"): 11,
    ("Alamo Square", "Financial District"): 17,
    ("Alamo Square", "Sunset District"): 16,
    ("Financial District", "The Castro"): 20,
    ("Financial District", "Marina District"): 15,
    ("Financial District", "Presidio"): 22,
    ("Financial District", "North Beach"): 7,
    ("Financial District", "Embarcadero"): 4,
    ("Financial District", "Haight-Ashbury"): 19,
    ("Financial District", "Golden Gate Park"): 23,
    ("Financial District", "Richmond District"): 21,
    ("Financial District", "Alamo Square"): 17,
    ("Financial District", "Sunset District"): 30,
    ("Sunset District", "The Castro"): 17,
    ("Sunset District", "Marina District"): 21,
    ("Sunset District", "Presidio"): 16,
    ("Sunset District", "North Beach"): 28,
    ("Sunset District", "Embarcadero"): 30,
    ("Sunset District", "Haight-Ashbury"): 15,
    ("Sunset District", "Golden Gate Park"): 11,
    ("Sunset District", "Richmond District"): 12,
    ("Sunset District", "Alamo Square"): 17,
    ("Sunset District", "Financial District"): 30,
}

# Define the friends and their availability
friends = {
    "Elizabeth": ("Marina District", 1900, 2045, 105),
    "Joshua": ("Presidio", 830, 1315, 105),
    "Timothy": ("North Beach", 1945, 2200, 90),
    "David": ("Embarcadero", 1045, 1230, 30),
    "Kimberly": ("Haight-Ashbury", 1645, 2130, 75),
    "Lisa": ("Golden Gate Park", 1730, 2145, 45),
    "Ronald": ("Richmond District", 800, 930, 90),
    "Stephanie": ("Alamo Square", 1530, 1630, 30),
    "Helen": ("Financial District", 1730, 1830, 45),
    "Laura": ("Sunset District", 1745, 2115, 90),
}

# Create a solver instance
solver = Solver()

# Define the variables
current_location = String('current_location')
current_time = Int('current_time')
meetings = []

# Initial location and time
solver.add(current_location == "The Castro")
solver.add(current_time == 900)

# Define the meeting variables
for friend, (location, start, end, duration) in friends.items():
    meet_start = Int(f'{friend}_start')
    meet_end = Int(f'{friend}_end')
    meet = Bool(f'meet_{friend}')
    meetings.append((friend, meet_start, meet_end, meet))
    
    # Constraints for meeting
    solver.add(meet_start >= start)
    solver.add(meet_end <= end)
    solver.add(meet_end - meet_start >= duration)
    solver.add(meet_start >= current_time + travel_times[(current_location, location)])
    solver.add(meet_end <= 2359)
    
    # Update current location and time if meeting
    solver.add(Implies(meet, current_location == location))
    solver.add(Implies(meet, current_time == meet_end))
    
    # Ensure no overlapping meetings
    for other_friend, other_meet_start, other_meet_end, other_meet in meetings[:-1]:
        solver.add(Or(meet_start >= other_meet_end, other_meet_start >= meet_end))

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    result = []
    for friend, meet_start, meet_end, meet in meetings:
        if model.evaluate(meet):
            start_time = model.evaluate(meet_start).as_long()
            end_time = model.evaluate(meet_end).as_long()
            result.append({
                "action": "meet",
                "person": friend,
                "start_time": f"{start_time // 100:02}:{start_time % 100:02}",
                "end_time": f"{end_time // 100:02}:{end_time % 100:02}"
            })
    print({"itinerary": result})
else:
    print("No solution found")