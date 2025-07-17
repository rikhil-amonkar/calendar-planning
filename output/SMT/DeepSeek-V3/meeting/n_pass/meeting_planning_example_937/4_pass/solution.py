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

    # Create ordering variables and constraints
    people = list(friends.keys())
    n = len(people)
    
    # Create a matrix of ordering variables
    order = [[Bool(f"order_{i}_{j}") for j in range(n)] for i in range(n)]
    
    # Add constraints for the ordering variables
    for i in range(n):
        for j in range(n):
            if i != j:
                # If i comes before j, then j's start must be after i's end plus travel time
                loc_i = meeting_vars[people[i]]["location"]
                loc_j = meeting_vars[people[j]]["location"]
                travel_time = travel_times[loc_i][loc_j]
                s.add(Implies(order[i][j], 
                          meeting_vars[people[j]]["start"] >= meeting_vars[people[i]]["end"] + travel_time))
    
    # Ensure the ordering is transitive and complete
    for i in range(n):
        for j in range(n):
            if i != j:
                for k in range(n):
                    if i != k and j != k:
                        s.add(Implies(And(order[i][j], order[j][k]), order[i][k]))
                s.add(Or(order[i][j], order[j][i]))
    
    # Exactly one meeting must be first (after traveling from Russian Hill)
    first_meeting = [Bool(f"first_{i}") for i in range(n)]
    s.add(Sum([If(first_meeting[i], 1, 0) for i in range(n)) == 1)
    
    for i in range(n):
        loc = meeting_vars[people[i]]["location"]
        travel_time = travel_times[initial_location][loc]
        s.add(Implies(first_meeting[i], 
                  meeting_vars[people[i]]["start"] >= initial_time + travel_time))
        
        # All other meetings must come after some meeting
        s.add(Implies(Not(first_meeting[i]),
                  Or([And(order[j][i], first_meeting[j]) for j in range(n) if j != i])))

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
        # If no solution found, try relaxing some constraints
        # First try reducing meeting durations
        for person in meeting_vars:
            if friends[person]["min_duration"] > 15:
                s.add(meeting_vars[person]["end"] - meeting_vars[person]["start"] >= 15)
        
        if s.check() == sat:
            m = s.model()
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
            itinerary.sort(key=lambda x: x["start_time"])
            return {"itinerary": itinerary, "note": "Some meeting durations were reduced to find a feasible schedule"}
        else:
            return {"error": "No valid schedule found even after relaxing constraints"}

# Solve the problem and print the solution
solution = solve_scheduling_problem()
print("SOLUTION:")
print(json.dumps(solution, indent=2))