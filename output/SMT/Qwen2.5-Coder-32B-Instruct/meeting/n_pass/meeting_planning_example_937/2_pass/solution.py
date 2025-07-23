from z3 import *

# Define the locations and their travel times
locations = [
    "Russian Hill", "Sunset District", "Union Square", "Nob Hill", "Marina District",
    "Richmond District", "Financial District", "Embarcadero", "The Castro", "Alamo Square", "Presidio"
]

travel_times = {
    ("Russian Hill", "Sunset District"): 23,
    ("Russian Hill", "Union Square"): 10,
    ("Russian Hill", "Nob Hill"): 5,
    ("Russian Hill", "Marina District"): 7,
    ("Russian Hill", "Richmond District"): 14,
    ("Russian Hill", "Financial District"): 11,
    ("Russian Hill", "Embarcadero"): 8,
    ("Russian Hill", "The Castro"): 21,
    ("Russian Hill", "Alamo Square"): 15,
    ("Russian Hill", "Presidio"): 14,
    ("Sunset District", "Russian Hill"): 24,
    ("Sunset District", "Union Square"): 30,
    ("Sunset District", "Nob Hill"): 27,
    ("Sunset District", "Marina District"): 21,
    ("Sunset District", "Richmond District"): 12,
    ("Sunset District", "Financial District"): 30,
    ("Sunset District", "Embarcadero"): 30,
    ("Sunset District", "The Castro"): 17,
    ("Sunset District", "Alamo Square"): 17,
    ("Sunset District", "Presidio"): 16,
    ("Union Square", "Russian Hill"): 13,
    ("Union Square", "Sunset District"): 27,
    ("Union Square", "Nob Hill"): 9,
    ("Union Square", "Marina District"): 18,
    ("Union Square", "Richmond District"): 20,
    ("Union Square", "Financial District"): 9,
    ("Union Square", "Embarcadero"): 11,
    ("Union Square", "The Castro"): 17,
    ("Union Square", "Alamo Square"): 15,
    ("Union Square", "Presidio"): 24,
    ("Nob Hill", "Russian Hill"): 5,
    ("Nob Hill", "Sunset District"): 24,
    ("Nob Hill", "Union Square"): 7,
    ("Nob Hill", "Marina District"): 11,
    ("Nob Hill", "Richmond District"): 14,
    ("Nob Hill", "Financial District"): 9,
    ("Nob Hill", "Embarcadero"): 9,
    ("Nob Hill", "The Castro"): 17,
    ("Nob Hill", "Alamo Square"): 11,
    ("Nob Hill", "Presidio"): 17,
    ("Marina District", "Russian Hill"): 8,
    ("Marina District", "Sunset District"): 19,
    ("Marina District", "Union Square"): 16,
    ("Marina District", "Nob Hill"): 12,
    ("Marina District", "Richmond District"): 11,
    ("Marina District", "Financial District"): 17,
    ("Marina District", "Embarcadero"): 14,
    ("Marina District", "The Castro"): 22,
    ("Marina District", "Alamo Square"): 15,
    ("Marina District", "Presidio"): 10,
    ("Richmond District", "Russian Hill"): 13,
    ("Richmond District", "Sunset District"): 11,
    ("Richmond District", "Union Square"): 21,
    ("Richmond District", "Nob Hill"): 17,
    ("Richmond District", "Marina District"): 9,
    ("Richmond District", "Financial District"): 22,
    ("Richmond District", "Embarcadero"): 19,
    ("Richmond District", "The Castro"): 16,
    ("Richmond District", "Alamo Square"): 13,
    ("Richmond District", "Presidio"): 7,
    ("Financial District", "Russian Hill"): 11,
    ("Financial District", "Sunset District"): 30,
    ("Financial District", "Union Square"): 9,
    ("Financial District", "Nob Hill"): 8,
    ("Financial District", "Marina District"): 15,
    ("Financial District", "Richmond District"): 21,
    ("Financial District", "Embarcadero"): 4,
    ("Financial District", "The Castro"): 20,
    ("Financial District", "Alamo Square"): 17,
    ("Financial District", "Presidio"): 22,
    ("Embarcadero", "Russian Hill"): 8,
    ("Embarcadero", "Sunset District"): 30,
    ("Embarcadero", "Union Square"): 10,
    ("Embarcadero", "Nob Hill"): 10,
    ("Embarcadero", "Marina District"): 12,
    ("Embarcadero", "Richmond District"): 21,
    ("Embarcadero", "Financial District"): 5,
    ("Embarcadero", "The Castro"): 25,
    ("Embarcadero", "Alamo Square"): 19,
    ("Embarcadero", "Presidio"): 20,
    ("The Castro", "Russian Hill"): 18,
    ("The Castro", "Sunset District"): 17,
    ("The Castro", "Union Square"): 19,
    ("The Castro", "Nob Hill"): 16,
    ("The Castro", "Marina District"): 21,
    ("The Castro", "Richmond District"): 16,
    ("The Castro", "Financial District"): 21,
    ("The Castro", "Embarcadero"): 22,
    ("The Castro", "Alamo Square"): 8,
    ("The Castro", "Presidio"): 20,
    ("Alamo Square", "Russian Hill"): 13,
    ("Alamo Square", "Sunset District"): 16,
    ("Alamo Square", "Union Square"): 14,
    ("Alamo Square", "Nob Hill"): 11,
    ("Alamo Square", "Marina District"): 15,
    ("Alamo Square", "Richmond District"): 11,
    ("Alamo Square", "Financial District"): 17,
    ("Alamo Square", "Embarcadero"): 16,
    ("Alamo Square", "The Castro"): 8,
    ("Alamo Square", "Presidio"): 17,
    ("Presidio", "Russian Hill"): 14,
    ("Presidio", "Sunset District"): 15,
    ("Presidio", "Union Square"): 22,
    ("Presidio", "Nob Hill"): 18,
    ("Presidio", "Marina District"): 11,
    ("Presidio", "Richmond District"): 7,
    ("Presidio", "Financial District"): 23,
    ("Presidio", "Embarcadero"): 20,
    ("Presidio", "The Castro"): 21,
    ("Presidio", "Alamo Square"): 19,
}

# Define the friends and their availability
friends = {
    "David": ("Sunset District", 9.25, 22.00, 15),
    "Kenneth": ("Union Square", 21.25, 22.75, 15),
    "Patricia": ("Nob Hill", 15.00, 19.25, 120),
    "Mary": ("Marina District", 14.75, 16.75, 45),
    "Charles": ("Richmond District", 17.25, 21.00, 15),
    "Joshua": ("Financial District", 14.50, 17.25, 90),
    "Ronald": ("Embarcadero", 18.25, 20.75, 30),
    "George": ("The Castro", 14.25, 19.00, 105),
    "Kimberly": ("Alamo Square", 9.00, 14.50, 105),
    "William": ("Presidio", 7.00, 12.75, 60),
}

# Create a solver instance
solver = Solver()

# Define the variables
current_location = String('current_location')
current_time = Real('current_time')
meetings = []

# Add initial constraints
solver.add(current_location == "Russian Hill")
solver.add(current_time == 9.00)

# Define the meeting variables and constraints
for friend, (location, start, end, duration) in friends.items():
    meet_start = Real(f'meet_start_{friend}')
    meet_end = Real(f'meet_end_{friend}')
    meet = Bool(f'meet_{friend}')
    meetings.append((friend, meet_start, meet_end, meet, location))
    
    # Constraints for meeting
    solver.add(meet_start >= start)
    solver.add(meet_end <= end)
    solver.add(meet_end - meet_start >= duration / 60)
    solver.add(meet_start >= current_time + If(current_location == location, 0, travel_times[(current_location, location)] / 60))
    solver.add(meet_end <= 24.00)
    
    # Update current location and time if meeting
    solver.add(Implies(meet, current_location == location))
    solver.add(Implies(meet, current_time == meet_end))
    
    # Ensure no overlapping meetings
    for other_friend, other_meet_start, other_meet_end, other_meet, other_location in meetings[:-1]:
        solver.add(Or(meet_start >= other_meet_end, other_meet_start >= meet_end))

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    result = []
    for friend, meet_start, meet_end, meet, location in meetings:
        if model[meet]:
            start_time = model[meet_start].as_decimal(2)
            end_time = model[meet_end].as_decimal(2)
            result.append({
                "action": "meet",
                "person": friend,
                "start_time": f"{int(start_time):02}:{int((start_time % 1) * 60):02}",
                "end_time": f"{int(end_time):02}:{int((end_time % 1) * 60):02}"
            })
    result = sorted(result, key=lambda x: x["start_time"])
    print(f'SOLUTION: {{"itinerary": {result}}}')
else:
    print("No solution found")