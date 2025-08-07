from z3 import *
import json
from itertools import combinations

def solve_scheduling_problem():
    solver = Optimize()

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

    # Define travel times (in minutes) - with consistent location names
    travel_times = {
        "The Castro": {
            "Marina District": 21, "Presidio": 20, "North Beach": 20, "Embarcadero": 22,
            "Haight-Ashbury": 6, "Golden Gate Park": 11, "Richmond District": 16,
            "Alamo Square": 8, "Financial District": 21, "Sunset District": 17
        },
        "Marina District": {
            "The Castro": 22, "Presidio": 10, "North Beach": 11, "Embarcadero": 14,
            "Haight-Ashbury": 16, "Golden Gate Park": 18, "Richmond District": 11,
            "Alamo Square": 15, "Financial District": 17, "Sunset District": 19
        },
        "Presidio": {
            "The Castro": 21, "Marina District": 11, "North Beach": 18, "Embarcadero": 20,
            "Haight-Ashbury": 15, "Golden Gate Park": 12, "Richmond District": 7,
            "Alamo Square": 19, "Financial District": 23, "Sunset District": 15
        },
        "North Beach": {
            "The Castro": 23, "Marina District": 9, "Presidio": 17, "Embarcadero": 6,
            "Haight-Ashbury": 18, "Golden Gate Park": 22, "Richmond District": 18,
            "Alamo Square": 16, "Financial District": 8, "Sunset District": 27
        },
        "Embarcadero": {
            "The Castro": 25, "Marina District": 12, "Presidio": 20, "North Beach": 5,
            "Haight-Ashbury": 21, "Golden Gate Park": 25, "Richmond District": 21,
            "Alamo Square": 19, "Financial District": 5, "Sunset District": 30
        },
        "Haight-Ashbury": {
            "The Castro": 6, "Marina District": 17, "Presidio": 15, "North Beach": 19,
            "Embarcadero": 20, "Golden Gate Park": 7, "Richmond District": 10,
            "Alamo Square": 5, "Financial District": 21, "Sunset District": 15
        },
        "Golden Gate Park": {
            "The Castro": 13, "Marina District": 16, "Presidio": 11, "North Beach": 23,
            "Embarcadero": 25, "Haight-Ashbury": 7, "Richmond District": 7,
            "Alamo Square": 9, "Financial District": 26, "Sunset District": 10
        },
        "Richmond District": {
            "The Castro": 16, "Marina District": 9, "Presidio": 7, "North Beach": 17,
            "Embarcadero": 19, "Haight-Ashbury": 10, "Golden Gate Park": 9,
            "Alamo Square": 13, "Financial District": 22, "Sunset District": 11
        },
        "Alamo Square": {
            "The Castro": 8, "Marina District": 15, "Presidio": 17, "North Beach": 15,
            "Embarcadero": 16, "Haight-Ashbury": 5, "Golden Gate Park": 9,
            "Richmond District": 11, "Financial District": 17, "Sunset District": 16
        },
        "Financial District": {
            "The Castro": 20, "Marina District": 15, "Presidio": 22, "North Beach": 7,
            "Embarcadero": 4, "Haight-Ashbury": 19, "Golden Gate Park": 23,
            "Richmond District": 21, "Alamo Square": 17, "Sunset District": 30
        },
        "Sunset District": {
            "The Castro": 17, "Marina District": 21, "Presidio": 16, "North Beach": 28,
            "Embarcadero": 30, "Haight-Ashbury": 15, "Golden Gate Park": 11,
            "Richmond District": 12, "Alamo Square": 17, "Financial District": 30
        }
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
    for i in range(len(friends)):
        for j in range(len(friends)):
            if i != j:
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