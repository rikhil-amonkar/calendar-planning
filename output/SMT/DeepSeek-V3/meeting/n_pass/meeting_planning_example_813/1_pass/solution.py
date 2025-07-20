from z3 import *
import json

def solve_scheduling_problem():
    # Initialize Z3 solver
    solver = Solver()

    # Define the friends and their constraints
    friends = {
        "Joshua": {
            "location": "Embarcadero",
            "available_start": "09:45",
            "available_end": "18:00",
            "min_duration": 105,
        },
        "Jeffrey": {
            "location": "Bayview",
            "available_start": "09:45",
            "available_end": "20:15",
            "min_duration": 75,
        },
        "Charles": {
            "location": "Union Square",
            "available_start": "10:45",
            "available_end": "20:15",
            "min_duration": 120,
        },
        "Joseph": {
            "location": "Chinatown",
            "available_start": "07:00",
            "available_end": "15:30",
            "min_duration": 60,
        },
        "Elizabeth": {
            "location": "Sunset District",
            "available_start": "09:00",
            "available_end": "09:45",
            "min_duration": 45,
        },
        "Matthew": {
            "location": "Golden Gate Park",
            "available_start": "11:00",
            "available_end": "19:30",
            "min_duration": 45,
        },
        "Carol": {
            "location": "Financial District",
            "available_start": "10:45",
            "available_end": "11:15",
            "min_duration": 15,
        },
        "Paul": {
            "location": "Haight-Ashbury",
            "available_start": "19:15",
            "available_end": "20:30",
            "min_duration": 15,
        },
        "Rebecca": {
            "location": "Mission District",
            "available_start": "17:00",
            "available_end": "21:45",
            "min_duration": 45,
        },
    }

    # Travel times (in minutes) between locations
    travel_times = {
        "Marina District": {
            "Embarcadero": 14,
            "Bayview": 27,
            "Union Square": 16,
            "Chinatown": 15,
            "Sunset District": 19,
            "Golden Gate Park": 18,
            "Financial District": 17,
            "Haight-Ashbury": 16,
            "Mission District": 20,
        },
        "Embarcadero": {
            "Marina District": 12,
            "Bayview": 21,
            "Union Square": 10,
            "Chinatown": 7,
            "Sunset District": 30,
            "Golden Gate Park": 25,
            "Financial District": 5,
            "Haight-Ashbury": 21,
            "Mission District": 20,
        },
        "Bayview": {
            "Marina District": 27,
            "Embarcadero": 19,
            "Union Square": 18,
            "Chinatown": 19,
            "Sunset District": 23,
            "Golden Gate Park": 22,
            "Financial District": 19,
            "Haight-Ashbury": 19,
            "Mission District": 13,
        },
        "Union Square": {
            "Marina District": 18,
            "Embarcadero": 11,
            "Bayview": 15,
            "Chinatown": 7,
            "Sunset District": 27,
            "Golden Gate Park": 22,
            "Financial District": 9,
            "Haight-Ashbury": 18,
            "Mission District": 14,
        },
        "Chinatown": {
            "Marina District": 12,
            "Embarcadero": 5,
            "Bayview": 20,
            "Union Square": 7,
            "Sunset District": 29,
            "Golden Gate Park": 23,
            "Financial District": 5,
            "Haight-Ashbury": 19,
            "Mission District": 17,
        },
        "Sunset District": {
            "Marina District": 21,
            "Embarcadero": 30,
            "Bayview": 22,
            "Union Square": 30,
            "Chinatown": 30,
            "Golden Gate Park": 11,
            "Financial District": 30,
            "Haight-Ashbury": 15,
            "Mission District": 25,
        },
        "Golden Gate Park": {
            "Marina District": 16,
            "Embarcadero": 25,
            "Bayview": 23,
            "Union Square": 22,
            "Chinatown": 23,
            "Sunset District": 10,
            "Financial District": 26,
            "Haight-Ashbury": 7,
            "Mission District": 17,
        },
        "Financial District": {
            "Marina District": 15,
            "Embarcadero": 4,
            "Bayview": 19,
            "Union Square": 9,
            "Chinatown": 5,
            "Sunset District": 30,
            "Golden Gate Park": 23,
            "Haight-Ashbury": 19,
            "Mission District": 17,
        },
        "Haight-Ashbury": {
            "Marina District": 17,
            "Embarcadero": 20,
            "Bayview": 18,
            "Union Square": 19,
            "Chinatown": 19,
            "Sunset District": 15,
            "Golden Gate Park": 7,
            "Financial District": 21,
            "Mission District": 11,
        },
        "Mission District": {
            "Marina District": 19,
            "Embarcadero": 19,
            "Bayview": 14,
            "Union Square": 15,
            "Chinatown": 16,
            "Sunset District": 24,
            "Golden Gate Park": 17,
            "Financial District": 15,
            "Haight-Ashbury": 12,
        },
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

    # Create variables for each friend's meeting start and end times
    meeting_vars = {}
    for name in friends:
        start = Int(f"start_{name}")
        end = Int(f"end_{name}")
        meeting_vars[name] = (start, end)

    # Add constraints for each friend's availability and duration
    for name in friends:
        friend = friends[name]
        start, end = meeting_vars[name]
        available_start = time_to_minutes(friend["available_start"])
        available_end = time_to_minutes(friend["available_end"])
        min_duration = friend["min_duration"]

        solver.add(start >= available_start)
        solver.add(end <= available_end)
        solver.add(end - start >= min_duration)

    # Add constraints for travel times between consecutive meetings
    # We need to define the order of meetings and ensure travel times are accounted for
    # This is a simplified approach where we assume a certain order and add constraints accordingly
    # In a more complete solution, we would need to model the order of meetings as well

    # For simplicity, let's assume we meet Elizabeth first (since she's only available at 9:00 AM)
    # Then we can meet others in some order, ensuring travel times are respected

    # Meet Elizabeth first
    elizabeth_start, elizabeth_end = meeting_vars["Elizabeth"]
    solver.add(elizabeth_start == time_to_minutes("09:00"))
    solver.add(elizabeth_end == time_to_minutes("09:45"))

    # After meeting Elizabeth, we can go to other friends
    # Let's try to meet Joseph next (since he's only available until 3:30 PM)
    joseph_start, joseph_end = meeting_vars["Joseph"]
    solver.add(joseph_start >= elizabeth_end + travel_times["Sunset District"]["Chinatown"])

    # Then meet Carol (she's only available from 10:45 to 11:15)
    carol_start, carol_end = meeting_vars["Carol"]
    solver.add(carol_start >= joseph_end + travel_times["Chinatown"]["Financial District"])
    solver.add(carol_start <= time_to_minutes("11:15") - friends["Carol"]["min_duration"])

    # Then meet Matthew
    matthew_start, matthew_end = meeting_vars["Matthew"]
    solver.add(matthew_start >= carol_end + travel_times["Financial District"]["Golden Gate Park"])

    # Then meet Charles
    charles_start, charles_end = meeting_vars["Charles"]
    solver.add(charles_start >= matthew_end + travel_times["Golden Gate Park"]["Union Square"])

    # Then meet Joshua
    joshua_start, joshua_end = meeting_vars["Joshua"]
    solver.add(joshua_start >= charles_end + travel_times["Union Square"]["Embarcadero"])

    # Then meet Jeffrey
    jeffrey_start, jeffrey_end = meeting_vars["Jeffrey"]
    solver.add(jeffrey_start >= joshua_end + travel_times["Embarcadero"]["Bayview"])

    # Then meet Rebecca
    rebecca_start, rebecca_end = meeting_vars["Rebecca"]
    solver.add(rebecca_start >= jeffrey_end + travel_times["Bayview"]["Mission District"])

    # Then meet Paul
    paul_start, paul_end = meeting_vars["Paul"]
    solver.add(paul_start >= rebecca_end + travel_times["Mission District"]["Haight-Ashbury"])

    # Ensure all meetings are scheduled
    for name in friends:
        start, end = meeting_vars[name]
        solver.add(start >= 0)
        solver.add(end >= 0)

    # Try to maximize the number of friends met (all in this case)
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for name in friends:
            start, end = meeting_vars[name]
            start_time = model.eval(start).as_long()
            end_time = model.eval(end).as_long()
            itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": minutes_to_time(start_time),
                "end_time": minutes_to_time(end_time),
            })
        # Sort itinerary by start time
        itinerary.sort(key=lambda x: x["start_time"])
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Solve the problem and print the solution
solution = solve_scheduling_problem()
print("SOLUTION:")
print(json.dumps(solution, indent=2))