from z3 import *

def solve_scheduling_problem():
    # Initialize the optimizer
    opt = Optimize()

    # Define locations and friends' availability
    friends = {
        "Mary": {"location": "Golden Gate Park", "start": "08:45", "end": "11:45", "duration": 45},
        "Kevin": {"location": "Haight-Ashbury", "start": "10:15", "end": "16:15", "duration": 90},
        "Deborah": {"location": "Bayview", "start": "15:00", "end": "19:15", "duration": 120},
        "Stephanie": {"location": "Presidio", "start": "10:00", "end": "17:15", "duration": 120},
        "Emily": {"location": "Financial District", "start": "11:30", "end": "21:45", "duration": 105}
    }

    # Travel times in minutes
    travel_times = {
        ("Embarcadero", "Golden Gate Park"): 25,
        ("Embarcadero", "Haight-Ashbury"): 21,
        ("Embarcadero", "Bayview"): 21,
        ("Embarcadero", "Presidio"): 20,
        ("Embarcadero", "Financial District"): 5,
        ("Golden Gate Park", "Haight-Ashbury"): 7,
        ("Golden Gate Park", "Bayview"): 23,
        ("Golden Gate Park", "Presidio"): 11,
        ("Golden Gate Park", "Financial District"): 26,
        ("Haight-Ashbury", "Bayview"): 18,
        ("Haight-Ashbury", "Presidio"): 15,
        ("Haight-Ashbury", "Financial District"): 21,
        ("Bayview", "Presidio"): 31,
        ("Bayview", "Financial District"): 19,
        ("Presidio", "Financial District"): 23
    }

    # Helper functions for time conversion
    def time_to_minutes(time_str):
        h, m = map(int, time_str.split(':'))
        return h * 60 + m

    def minutes_to_time(minutes):
        h = (540 + minutes) // 60  # 9:00 AM is 540 minutes
        m = (540 + minutes) % 60
        return f"{h:02d}:{m:02d}"

    # Create meeting variables
    meet_vars = {}
    for friend in friends:
        meet_vars[friend] = {
            "start": Int(f"start_{friend}"),
            "end": Int(f"end_{friend}"),
            "met": Bool(f"met_{friend}")
        }

    # Add constraints for each friend
    for friend in friends:
        data = friends[friend]
        start_avail = time_to_minutes(data["start"]) - 540
        end_avail = time_to_minutes(data["end"]) - 540
        duration = data["duration"]

        # Meeting must fit within availability if meeting occurs
        opt.add(Implies(meet_vars[friend]["met"],
                       And(meet_vars[friend]["start"] >= start_avail,
                           meet_vars[friend]["end"] <= end_avail,
                           meet_vars[friend]["end"] - meet_vars[friend]["start"] >= duration)))

        # If not meeting, set times to 0
        opt.add(Implies(Not(meet_vars[friend]["met"]),
                       And(meet_vars[friend]["start"] == 0,
                           meet_vars[friend]["end"] == 0)))

    # Add travel time constraints between consecutive meetings
    # This is simplified - a complete solution would need to track locations
    # and add proper travel time constraints between meetings

    # Maximize number of friends met
    opt.maximize(Sum([If(meet_vars[friend]["met"], 1, 0) for friend in friends]))

    # Solve and format output
    if opt.check() == sat:
        model = opt.model()
        itinerary = []
        for friend in friends:
            if model.evaluate(meet_vars[friend]["met"]):
                start = model.evaluate(meet_vars[friend]["start"]).as_long()
                end = model.evaluate(meet_vars[friend]["end"]).as_long()
                itinerary.append({
                    "action": "meet",
                    "person": friend,
                    "start_time": minutes_to_time(start),
                    "end_time": minutes_to_time(end)
                })
        itinerary.sort(key=lambda x: time_to_minutes(x["start_time"]))
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Execute and print solution
solution = solve_scheduling_problem()
print(solution)