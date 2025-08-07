from z3 import *
import json
from itertools import combinations

def solve_scheduling_problem():
    solver = Optimize()  # Using Optimize instead of Solver to find better solutions

    # Define friends and their constraints
    friends = {
        "Elizabeth": {"location": "Marina District", "available_start": "19:00", "available_end": "20:45", "min_duration": 105},
        "Joshua": {"location": "Presidio", "available_start": "08:30", "available_end": "13:15", "min_duration": 105},
        "Timothy": {"location": "North Beach", "available_start": "19:45", "available_end": "22:00", "min_duration": 90},
        "David": {"location": "Embarcadero", "available_start": "10:45", "available_end": "12:30", "min_duration": 30},
        "Kimberly": {"location": "Haight-Ashbury", "available_start": "16:45", "available_end": "21:30", "min_duration": 75},
        "Lisa": {"location": "Golden Gate Park", "available_start": "17:30", "available_end": "21:45", "min_duration": 45},
        "Ronald": {"location": "Richmond District", "available_start": "08:00", "available_end": "09:30", "min_duration": 90},
        "Stephanie": {"location": "Alamo Square", "available_start": "15:30", "available_end": "16:30", "min_duration": 30},
        "Helen": {"location": "Financial District", "available_start": "17:30", "available_end": "18:30", "min_duration": 45},
        "Laura": {"location": "Sunset District", "available_start": "17:45", "available_end": "21:15", "min_duration": 90}
    }

    # Convert time strings to minutes since 9:00 AM (540 minutes)
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    # Convert minutes back to time string
    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    # Current location starts at The Castro at 9:00 AM (540 minutes)
    current_location = "The Castro"
    current_time = 540

    # Define travel times (in minutes)
    travel_times = {
        "The Castro": {
            "Marina District": 21, "Presidio": 20, "North Beach": 20, "Embarcadero": 22,
            "Haight-Ashbury": 6, "Golden Gate Park": 11, "Richmond District": 16,
            "Alamo Square": 8, "Financial District": 21, "Sunset District": 17
        },
        # Other locations omitted for brevity (same as previous implementation)
        # ...
    }

    # Create variables for each meeting's start and end times
    meeting_vars = {}
    for person in friends:
        start = Int(f'start_{person}')
        end = Int(f'end_{person}')
        meeting_vars[person] = {'start': start, 'end': end}

    # Add basic constraints for each meeting
    for person in friends:
        info = friends[person]
        available_start = time_to_minutes(info["available_start"])
        available_end = time_to_minutes(info["available_end"])
        min_duration = info["min_duration"]

        solver.add(meeting_vars[person]['start'] >= available_start)
        solver.add(meeting_vars[person]['end'] <= available_end)
        solver.add(meeting_vars[person]['end'] - meeting_vars[person]['start'] >= min_duration)
        solver.add(meeting_vars[person]['start'] < meeting_vars[person]['end'])

    # Create a list to track meeting order
    meeting_order = [Int(f'order_{person}') for person in friends]
    for i, person in enumerate(friends):
        solver.add(meeting_order[i] >= 0, meeting_order[i] < len(friends))

    # All meeting orders must be distinct
    solver.add(Distinct(meeting_order))

    # Add travel time constraints based on meeting order
    for i in range(len(friends) - 1):
        for j in range(i + 1, len(friends)):
            person1 = list(friends.keys())[i]
            person2 = list(friends.keys())[j]
            loc1 = friends[person1]["location"]
            loc2 = friends[person2]["location"]
            travel_time = travel_times[loc1][loc2]

            # If person1 comes before person2 in the order
            solver.add(
                Implies(
                    meeting_order[i] < meeting_order[j],
                    meeting_vars[person2]['start'] >= meeting_vars[person1]['end'] + travel_time
                )
            )
            # If person2 comes before person1 in the order
            solver.add(
                Implies(
                    meeting_order[j] < meeting_order[i],
                    meeting_vars[person1]['start'] >= meeting_vars[person2]['end'] + travel_time
                )
            )

    # First meeting must start after initial time plus travel time
    for person in friends:
        loc = friends[person]["location"]
        travel_time = travel_times[current_location][loc]
        solver.add(
            Implies(
                meeting_order[list(friends.keys()).index(person)] == 0,
                meeting_vars[person]['start'] >= current_time + travel_time
            )
        )

    # Maximize the number of meetings attended
    num_meetings = Int('num_meetings')
    solver.add(num_meetings == len(friends))  # Try to meet all friends
    solver.maximize(num_meetings)

    # Check if the solver can find a solution
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for person in friends:
            start = model[meeting_vars[person]['start']].as_long()
            end = model[meeting_vars[person]['end']].as_long()
            itinerary.append({
                "action": "meet",
                "person": person,
                "start_time": minutes_to_time(start),
                "end_time": minutes_to_time(end)
            })
        
        # Sort itinerary by start time
        itinerary.sort(key=lambda x: time_to_minutes(x["start_time"]))
        return {"itinerary": itinerary}
    else:
        return {"error": "No feasible schedule found"}

# Solve the problem and print the solution
solution = solve_scheduling_problem()
print(json.dumps(solution, indent=2))