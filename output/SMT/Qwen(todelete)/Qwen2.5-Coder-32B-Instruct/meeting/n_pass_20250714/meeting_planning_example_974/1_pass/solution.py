from z3 import *

# Define the locations
locations = ["Sunset District", "Presidio", "Nob Hill", "Pacific Heights", 
             "Mission District", "Marina District", "North Beach", "Russian Hill", 
             "Richmond District", "Embarcadero", "Alamo Square"]

# Define the travel times as a dictionary
travel_times = {
    ("Sunset District", "Presidio"): 16,
    ("Sunset District", "Nob Hill"): 27,
    ("Sunset District", "Pacific Heights"): 21,
    ("Sunset District", "Mission District"): 25,
    ("Sunset District", "Marina District"): 21,
    ("Sunset District", "North Beach"): 28,
    ("Sunset District", "Russian Hill"): 24,
    ("Sunset District", "Richmond District"): 12,
    ("Sunset District", "Embarcadero"): 30,
    ("Sunset District", "Alamo Square"): 17,
    ("Presidio", "Sunset District"): 15,
    ("Presidio", "Nob Hill"): 18,
    ("Presidio", "Pacific Heights"): 11,
    ("Presidio", "Mission District"): 26,
    ("Presidio", "Marina District"): 11,
    ("Presidio", "North Beach"): 18,
    ("Presidio", "Russian Hill"): 14,
    ("Presidio", "Richmond District"): 7,
    ("Presidio", "Embarcadero"): 20,
    ("Presidio", "Alamo Square"): 19,
    ("Nob Hill", "Sunset District"): 24,
    ("Nob Hill", "Presidio"): 17,
    ("Nob Hill", "Pacific Heights"): 8,
    ("Nob Hill", "Mission District"): 13,
    ("Nob Hill", "Marina District"): 11,
    ("Nob Hill", "North Beach"): 8,
    ("Nob Hill", "Russian Hill"): 5,
    ("Nob Hill", "Richmond District"): 14,
    ("Nob Hill", "Embarcadero"): 9,
    ("Nob Hill", "Alamo Square"): 11,
    ("Pacific Heights", "Sunset District"): 21,
    ("Pacific Heights", "Presidio"): 11,
    ("Pacific Heights", "Nob Hill"): 8,
    ("Pacific Heights", "Mission District"): 15,
    ("Pacific Heights", "Marina District"): 6,
    ("Pacific Heights", "North Beach"): 9,
    ("Pacific Heights", "Russian Hill"): 7,
    ("Pacific Heights", "Richmond District"): 12,
    ("Pacific Heights", "Embarcadero"): 10,
    ("Pacific Heights", "Alamo Square"): 10,
    ("Mission District", "Sunset District"): 24,
    ("Mission District", "Presidio"): 25,
    ("Mission District", "Nob Hill"): 12,
    ("Mission District", "Pacific Heights"): 16,
    ("Mission District", "Marina District"): 19,
    ("Mission District", "North Beach"): 17,
    ("Mission District", "Russian Hill"): 15,
    ("Mission District", "Richmond District"): 20,
    ("Mission District", "Embarcadero"): 19,
    ("Mission District", "Alamo Square"): 11,
    ("Marina District", "Sunset District"): 19,
    ("Marina District", "Presidio"): 10,
    ("Marina District", "Nob Hill"): 12,
    ("Marina District", "Pacific Heights"): 7,
    ("Marina District", "Mission District"): 20,
    ("Marina District", "North Beach"): 11,
    ("Marina District", "Russian Hill"): 8,
    ("Marina District", "Richmond District"): 11,
    ("Marina District", "Embarcadero"): 14,
    ("Marina District", "Alamo Square"): 15,
    ("North Beach", "Sunset District"): 27,
    ("North Beach", "Presidio"): 17,
    ("North Beach", "Nob Hill"): 7,
    ("North Beach", "Pacific Heights"): 8,
    ("North Beach", "Mission District"): 18,
    ("North Beach", "Marina District"): 9,
    ("North Beach", "Russian Hill"): 4,
    ("North Beach", "Richmond District"): 18,
    ("North Beach", "Embarcadero"): 6,
    ("North Beach", "Alamo Square"): 16,
    ("Russian Hill", "Sunset District"): 23,
    ("Russian Hill", "Presidio"): 14,
    ("Russian Hill", "Nob Hill"): 5,
    ("Russian Hill", "Pacific Heights"): 7,
    ("Russian Hill", "Mission District"): 16,
    ("Russian Hill", "Marina District"): 7,
    ("Russian Hill", "North Beach"): 5,
    ("Russian Hill", "Richmond District"): 14,
    ("Russian Hill", "Embarcadero"): 8,
    ("Russian Hill", "Alamo Square"): 15,
    ("Richmond District", "Sunset District"): 11,
    ("Richmond District", "Presidio"): 7,
    ("Richmond District", "Nob Hill"): 17,
    ("Richmond District", "Pacific Heights"): 10,
    ("Richmond District", "Mission District"): 20,
    ("Richmond District", "Marina District"): 9,
    ("Richmond District", "North Beach"): 17,
    ("Richmond District", "Russian Hill"): 13,
    ("Richmond District", "Embarcadero"): 19,
    ("Richmond District", "Alamo Square"): 13,
    ("Embarcadero", "Sunset District"): 30,
    ("Embarcadero", "Presidio"): 20,
    ("Embarcadero", "Nob Hill"): 10,
    ("Embarcadero", "Pacific Heights"): 11,
    ("Embarcadero", "Mission District"): 20,
    ("Embarcadero", "Marina District"): 12,
    ("Embarcadero", "North Beach"): 5,
    ("Embarcadero", "Russian Hill"): 8,
    ("Embarcadero", "Richmond District"): 21,
    ("Embarcadero", "Alamo Square"): 19,
    ("Alamo Square", "Sunset District"): 16,
    ("Alamo Square", "Presidio"): 17,
    ("Alamo Square", "Nob Hill"): 11,
    ("Alamo Square", "Pacific Heights"): 10,
    ("Alamo Square", "Mission District"): 10,
    ("Alamo Square", "Marina District"): 15,
    ("Alamo Square", "North Beach"): 15,
    ("Alamo Square", "Russian Hill"): 13,
    ("Alamo Square", "Richmond District"): 11,
    ("Alamo Square", "Embarcadero"): 16,
}

# Define the availability of each friend
availability = {
    "Charles": (("Presidio", 1335, 1800), 105),
    "Robert": (("Nob Hill", 1335, 1770), 90),
    "Nancy": (("Pacific Heights", 1485, 2400), 105),
    "Brian": (("Mission District", 1530, 2400), 60),
    "Kimberly": (("Marina District", 1700, 1905), 75),
    "David": (("North Beach", 1485, 1650), 75),
    "William": (("Russian Hill", 1230, 1875), 120),
    "Jeffrey": (("Richmond District", 1200, 1875), 45),
    "Karen": (("Embarcadero", 1335, 2085), 60),
    "Joshua": (("Alamo Square", 1905, 2400), 60),
}

# Create the solver
solver = Solver()

# Define the time variables for each location visit
time_vars = {loc: Int(f"time_{loc}") for loc in locations}

# Initial time at Sunset District
solver.add(time_vars["Sunset District"] == 540)  # 9:00 AM

# Add constraints for each friend's meeting
for friend, ((loc, start, end), duration) in availability.items():
    start_time_var = Int(f"start_{friend}")
    end_time_var = Int(f"end_{friend}")
    
    # Ensure the meeting starts within the friend's availability
    solver.add(start_time_var >= start)
    solver.add(end_time_var <= end)
    
    # Ensure the meeting duration is met
    solver.add(end_time_var - start_time_var >= duration)
    
    # Ensure the meeting happens after traveling to the location
    solver.add(start_time_var >= time_vars[loc] + travel_times[("Sunset District", loc)])
    
    # Update the time variable for the next location visit
    solver.add(time_vars[loc] + travel_times[("Sunset District", loc)] <= start_time_var)

# Optimize the number of friends met
num_friends_met = Int('num_friends_met')
solver.add(num_friends_met == Sum([If(And(time_vars[loc] + travel_times[("Sunset District", loc)] <= start, 
                                       time_vars[loc] + travel_times[("Sunset District", loc)] + duration <= end), 
                                      1, 0) 
                                 for loc, (start, end), duration in availability.values()]))

# Maximize the number of friends met
solver.maximize(num_friends_met)

# Check if the problem is solvable
if solver.check() == sat:
    model = solver.model()
    print("SOLUTION:")
    for friend, ((loc, start, end), duration) in availability.items():
        start_time = model.evaluate(Int(f"start_{friend}")).as_long()
        end_time = model.evaluate(Int(f"end_{friend}")).as_long()
        print(f"Meet {friend} at {loc} from {start_time // 60}:{start_time % 60:02d} to {end_time // 60}:{end_time % 60:02d}")
else:
    print("No solution found.")