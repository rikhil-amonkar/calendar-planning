from z3 import *
import json

def solve_scheduling_problem():
    # Initialize Z3 solver
    s = Solver()

    # Define the friends and their constraints
    friends = {
        "David": {
            "location": "Sunset District",
            "available_start": "09:15",
            "available_end": "22:00",
            "min_duration": 15
        },
        "Kenneth": {
            "location": "Union Square",
            "available_start": "21:15",
            "available_end": "21:45",
            "min_duration": 15
        },
        "Patricia": {
            "location": "Nob Hill",
            "available_start": "15:00",
            "available_end": "19:15",
            "min_duration": 120
        },
        "Mary": {
            "location": "Marina District",
            "available_start": "14:45",
            "available_end": "16:45",
            "min_duration": 45
        },
        "Charles": {
            "location": "Richmond District",
            "available_start": "17:15",
            "available_end": "21:00",
            "min_duration": 15
        },
        "Joshua": {
            "location": "Financial District",
            "available_start": "14:30",
            "available_end": "17:15",
            "min_duration": 90
        },
        "Ronald": {
            "location": "Embarcadero",
            "available_start": "18:15",
            "available_end": "20:45",
            "min_duration": 30
        },
        "George": {
            "location": "The Castro",
            "available_start": "14:15",
            "available_end": "19:00",
            "min_duration": 105
        },
        "Kimberly": {
            "location": "Alamo Square",
            "available_start": "09:00",
            "available_end": "14:30",
            "min_duration": 105
        },
        "William": {
            "location": "Presidio",
            "available_start": "07:00",
            "available_end": "12:45",
            "min_duration": 60
        }
    }

    # Travel times (in minutes) from each location to another
    travel_times = {
        "Russian Hill": {
            "Sunset District": 23,
            "Union Square": 10,
            "Nob Hill": 5,
            "Marina District": 7,
            "Richmond District": 14,
            "Financial District": 11,
            "Embarcadero": 8,
            "The Castro": 21,
            "Alamo Square": 15,
            "Presidio": 14
        },
        "Sunset District": {
            "Russian Hill": 24,
            "Union Square": 30,
            "Nob Hill": 27,
            "Marina District": 21,
            "Richmond District": 12,
            "Financial District": 30,
            "Embarcadero": 30,
            "The Castro": 17,
            "Alamo Square": 17,
            "Presidio": 16
        },
        "Union Square": {
            "Russian Hill": 13,
            "Sunset District": 27,
            "Nob Hill": 9,
            "Marina District": 18,
            "Richmond District": 20,
            "Financial District": 9,
            "Embarcadero": 11,
            "The Castro": 17,
            "Alamo Square": 15,
            "Presidio": 24
        },
        "Nob Hill": {
            "Russian Hill": 5,
            "Sunset District": 24,
            "Union Square": 7,
            "Marina District": 11,
            "Richmond District": 14,
            "Financial District": 9,
            "Embarcadero": 9,
            "The Castro": 17,
            "Alamo Square": 11,
            "Presidio": 17
        },
        "Marina District": {
            "Russian Hill": 8,
            "Sunset District": 19,
            "Union Square": 16,
            "Nob Hill": 12,
            "Richmond District": 11,
            "Financial District": 17,
            "Embarcadero": 14,
            "The Castro": 22,
            "Alamo Square": 15,
            "Presidio": 10
        },
        "Richmond District": {
            "Russian Hill": 13,
            "Sunset District": 11,
            "Union Square": 21,
            "Nob Hill": 17,
            "Marina District": 9,
            "Financial District": 22,
            "Embarcadero": 19,
            "The Castro": 16,
            "Alamo Square": 13,
            "Presidio": 7
        },
        "Financial District": {
            "Russian Hill": 11,
            "Sunset District": 30,
            "Union Square": 9,
            "Nob Hill": 8,
            "Marina District": 15,
            "Richmond District": 21,
            "Embarcadero": 4,
            "The Castro": 20,
            "Alamo Square": 17,
            "Presidio": 22
        },
        "Embarcadero": {
            "Russian Hill": 8,
            "Sunset District": 30,
            "Union Square": 10,
            "Nob Hill": 10,
            "Marina District": 12,
            "Richmond District": 21,
            "Financial District": 5,
            "The Castro": 25,
            "Alamo Square": 19,
            "Presidio": 20
        },
        "The Castro": {
            "Russian Hill": 18,
            "Sunset District": 17,
            "Union Square": 19,
            "Nob Hill": 16,
            "Marina District": 21,
            "Richmond District": 16,
            "Financial District": 21,
            "Embarcadero": 22,
            "Alamo Square": 8,
            "Presidio": 20
        },
        "Alamo Square": {
            "Russian Hill": 13,
            "Sunset District": 16,
            "Union Square": 14,
            "Nob Hill": 11,
            "Marina District": 15,
            "Richmond District": 11,
            "Financial District": 17,
            "Embarcadero": 16,
            "The Castro": 8,
            "Presidio": 17
        },
        "Presidio": {
            "Russian Hill": 14,
            "Sunset District": 15,
            "Union Square": 22,
            "Nob Hill": 18,
            "Marina District": 11,
            "Richmond District": 7,
            "Financial District": 23,
            "Embarcadero": 20,
            "The Castro": 21,
            "Alamo Square": 19
        }
    }

    # Convert time strings to minutes since 9:00 AM (540 minutes)
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm - 540  # 9:00 AM is 540 minutes

    # Convert minutes back to time string
    def minutes_to_time(minutes):
        total_minutes = 540 + minutes
        hh = total_minutes // 60
        mm = total_minutes % 60
        return f"{hh:02d}:{mm:02d}"

    # Create variables for each meeting's start and end times
    meeting_vars = {}
    for person in friends:
        start = Int(f"start_{person}")
        end = Int(f"end_{person}")
        meeting_vars[person] = {
            "start": start,
            "end": end,
            "location": friends[person]["location"],
            "available_start": time_to_minutes(friends[person]["available_start"]),
            "available_end": time_to_minutes(friends[person]["available_end"]),
            "min_duration": friends[person]["min_duration"]
        }
        # Add constraints for meeting times within availability
        s.add(start >= meeting_vars[person]["available_start"])
        s.add(end <= meeting_vars[person]["available_end"])
        s.add(end - start >= meeting_vars[person]["min_duration"])

    # Initial location is Russian Hill at time 0 (9:00 AM)
    initial_location = "Russian Hill"
    initial_time = 0

    # Create constraints to ensure meetings don't overlap and account for travel times
    people = list(friends.keys())
    n = len(people)

    # Create a list to store all possible ordering constraints
    ordering_constraints = []

    # For each pair of meetings, create constraints to ensure proper ordering
    for i in range(n):
        for j in range(i+1, n):
            person1 = people[i]
            person2 = people[j]
            loc1 = meeting_vars[person1]["location"]
            loc2 = meeting_vars[person2]["location"]
            travel1to2 = travel_times[loc1][loc2]
            travel2to1 = travel_times[loc2][loc1]
            
            # Create a boolean variable to represent the ordering
            order_var = Bool(f"order_{person1}_{person2}")
            
            # Add constraints that enforce the ordering
            s.add(Implies(order_var, meeting_vars[person2]["start"] >= meeting_vars[person1]["end"] + travel1to2))
            s.add(Implies(Not(order_var), meeting_vars[person1]["start"] >= meeting_vars[person2]["end"] + travel2to1))
            
            ordering_constraints.append(order_var)

    # Add constraints for the first meeting (must be after travel from Russian Hill)
    first_meeting_constraints = []
    for person in people:
        loc = meeting_vars[person]["location"]
        travel = travel_times[initial_location][loc]
        first_meeting_constraints.append(
            meeting_vars[person]["start"] >= initial_time + travel
        )
    s.add(Or(first_meeting_constraints))

    # Check if the solution is satisfiable
    if s.check() == sat:
        m = s.model()
        # Extract the meeting times
        itinerary = []
        for person in meeting_vars:
            start_val = m[meeting_vars[person]["start"]].as_long()
            end_val = m[meeting_vars[person]["end"]].as_long()
            itinerary.append({
                "action": "meet",
                "person": person,
                "start_time": minutes_to_time(start_val),
                "end_time": minutes_to_time(end_val)
            })
        # Sort the itinerary by start time
        itinerary.sort(key=lambda x: x["start_time"])
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid schedule found"}

# Solve the problem and print the solution
solution = solve_scheduling_problem()
print("SOLUTION:")
print(json.dumps(solution, indent=2))