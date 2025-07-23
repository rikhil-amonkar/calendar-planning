from z3 import *
import json

def solve_scheduling_problem():
    # Initialize Z3 optimizer
    opt = Optimize()

    # Define the friends and their details
    friends = {
        "Mary": {
            "location": "Golden Gate Park",
            "available_start": "8:45",
            "available_end": "11:45",
            "min_duration": 45,
        },
        "Kevin": {
            "location": "Haight-Ashbury",
            "available_start": "10:15",
            "available_end": "16:15",
            "min_duration": 90,
        },
        "Deborah": {
            "location": "Bayview",
            "available_start": "15:00",
            "available_end": "19:15",
            "min_duration": 120,
        },
        "Stephanie": {
            "location": "Presidio",
            "available_start": "10:00",
            "available_end": "17:15",
            "min_duration": 120,
        },
        "Emily": {
            "location": "Financial District",
            "available_start": "11:30",
            "available_end": "21:45",
            "min_duration": 105,
        }
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

    # Define travel times between locations
    travel_times = {
        ("Embarcadero", "Golden Gate Park"): 25,
        ("Embarcadero", "Haight-Ashbury"): 21,
        ("Embarcadero", "Bayview"): 21,
        ("Embarcadero", "Presidio"): 20,
        ("Embarcadero", "Financial District"): 5,
        ("Golden Gate Park", "Embarcadero"): 25,
        ("Golden Gate Park", "Haight-Ashbury"): 7,
        ("Golden Gate Park", "Bayview"): 23,
        ("Golden Gate Park", "Presidio"): 11,
        ("Golden Gate Park", "Financial District"): 26,
        ("Haight-Ashbury", "Embarcadero"): 20,
        ("Haight-Ashbury", "Golden Gate Park"): 7,
        ("Haight-Ashbury", "Bayview"): 18,
        ("Haight-Ashbury", "Presidio"): 15,
        ("Haight-Ashbury", "Financial District"): 21,
        ("Bayview", "Embarcadero"): 19,
        ("Bayview", "Golden Gate Park"): 22,
        ("Bayview", "Haight-Ashbury"): 19,
        ("Bayview", "Presidio"): 31,
        ("Bayview", "Financial District"): 19,
        ("Presidio", "Embarcadero"): 20,
        ("Presidio", "Golden Gate Park"): 12,
        ("Presidio", "Haight-Ashbury"): 15,
        ("Presidio", "Bayview"): 31,
        ("Presidio", "Financial District"): 23,
        ("Financial District", "Embarcadero"): 4,
        ("Financial District", "Golden Gate Park"): 23,
        ("Financial District", "Haight-Ashbury"): 19,
        ("Financial District", "Bayview"): 19,
        ("Financial District", "Presidio"): 22,
    }

    # Current location starts at Embarcadero at 9:00 AM (540 minutes)
    current_time = 540  # 9:00 AM in minutes
    current_location = "Embarcadero"

    # Define variables for each friend's meeting start and end times
    meeting_vars = {}
    for name in friends:
        meeting_vars[name] = {
            "start": Int(f"start_{name}"),
            "end": Int(f"end_{name}"),
            "met": Bool(f"met_{name}")
        }

    # Constraints for each friend
    for name in friends:
        friend = friends[name]
        start_var = meeting_vars[name]["start"]
        end_var = meeting_vars[name]["end"]
        met_var = meeting_vars[name]["met"]

        available_start = time_to_minutes(friend["available_start"])
        available_end = time_to_minutes(friend["available_end"])
        min_duration = friend["min_duration"]

        # If meeting the friend, start and end must be within their availability
        opt.add(Implies(met_var, And(
            start_var >= available_start,
            end_var <= available_end,
            end_var == start_var + min_duration
        )))

        # If not meeting, start and end are 0
        opt.add(Implies(Not(met_var), And(start_var == 0, end_var == 0)))

    # Meeting order constraints: ensure no overlaps and travel times are respected
    # We'll model the sequence as Mary -> Kevin -> Stephanie -> Emily -> Deborah
    # Mary's meeting
    mary_met = meeting_vars["Mary"]["met"]
    mary_start = meeting_vars["Mary"]["start"]
    mary_end = meeting_vars["Mary"]["end"]
    mary_location = friends["Mary"]["location"]
    # Earliest start is 9:00 AM + travel time to Golden Gate Park (25 minutes)
    opt.add(Implies(mary_met, mary_start >= current_time + travel_times[(current_location, mary_location)]))
    opt.add(Implies(mary_met, mary_end <= time_to_minutes("11:45")))

    # Kevin's meeting
    kevin_met = meeting_vars["Kevin"]["met"]
    kevin_start = meeting_vars["Kevin"]["start"]
    kevin_end = meeting_vars["Kevin"]["end"]
    kevin_location = friends["Kevin"]["location"]
    # After Mary or directly from Embarcadero
    travel_to_kevin = If(mary_met, travel_times[(mary_location, kevin_location)], travel_times[(current_location, kevin_location)])
    opt.add(Implies(kevin_met, kevin_start >= If(mary_met, mary_end, current_time) + travel_to_kevin))

    # Stephanie's meeting
    stephanie_met = meeting_vars["Stephanie"]["met"]
    stephanie_start = meeting_vars["Stephanie"]["start"]
    stephanie_end = meeting_vars["Stephanie"]["end"]
    stephanie_location = friends["Stephanie"]["location"]
    # After Kevin or Mary
    travel_to_stephanie = If(kevin_met, travel_times[(kevin_location, stephanie_location)], 
                           If(mary_met, travel_times[(mary_location, stephanie_location)], 
                              travel_times[(current_location, stephanie_location)]))
    opt.add(Implies(stephanie_met, stephanie_start >= If(kevin_met, kevin_end, If(mary_met, mary_end, current_time)) + travel_to_stephanie))

    # Emily's meeting
    emily_met = meeting_vars["Emily"]["met"]
    emily_start = meeting_vars["Emily"]["start"]
    emily_end = meeting_vars["Emily"]["end"]
    emily_location = friends["Emily"]["location"]
    # After Stephanie or Kevin or Mary
    travel_to_emily = If(stephanie_met, travel_times[(stephanie_location, emily_location)],
                        If(kevin_met, travel_times[(kevin_location, emily_location)],
                           If(mary_met, travel_times[(mary_location, emily_location)],
                              travel_times[(current_location, emily_location)])))
    opt.add(Implies(emily_met, emily_start >= If(stephanie_met, stephanie_end, 
                                               If(kevin_met, kevin_end, 
                                                  If(mary_met, mary_end, current_time))) + travel_to_emily))

    # Deborah's meeting
    deborah_met = meeting_vars["Deborah"]["met"]
    deborah_start = meeting_vars["Deborah"]["start"]
    deborah_end = meeting_vars["Deborah"]["end"]
    deborah_location = friends["Deborah"]["location"]
    # After Emily or Stephanie or Kevin or Mary
    travel_to_deborah = If(emily_met, travel_times[(emily_location, deborah_location)],
                          If(stephanie_met, travel_times[(stephanie_location, deborah_location)],
                             If(kevin_met, travel_times[(kevin_location, deborah_location)],
                                If(mary_met, travel_times[(mary_location, deborah_location)],
                                   travel_times[(current_location, deborah_location)]))))
    opt.add(Implies(deborah_met, deborah_start >= If(emily_met, emily_end, 
                                                   If(stephanie_met, stephanie_end, 
                                                      If(kevin_met, kevin_end, 
                                                         If(mary_met, mary_end, current_time)))) + travel_to_deborah))

    # Maximize the number of friends met
    total_met = Sum([If(meeting_vars[name]["met"], 1, 0) for name in friends])
    opt.maximize(total_met)

    # Check if a solution exists
    if opt.check() == sat:
        model = opt.model()
        itinerary = []
        for name in friends:
            if model.evaluate(meeting_vars[name]["met"]):
                start = model.evaluate(meeting_vars[name]["start"])
                end = model.evaluate(meeting_vars[name]["end"])
                itinerary.append({
                    "action": "meet",
                    "person": name,
                    "start_time": minutes_to_time(start.as_long()),
                    "end_time": minutes_to_time(end.as_long())
                })
        # Sort itinerary by start time
        itinerary.sort(key=lambda x: time_to_minutes(x["start_time"]))
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Solve the problem and print the solution
solution = solve_scheduling_problem()
print(json.dumps(solution, indent=2))