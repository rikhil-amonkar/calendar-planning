from z3 import *

def solve_scheduling():
    # Initialize the solver
    s = Optimize()

    # Define the friends and their details
    friends = {
        "Jessica": {
            "location": "Golden Gate Park",
            "available_start": 13.75,  # 1:45 PM in decimal hours
            "available_end": 15.0,     # 3:00 PM
            "min_duration": 0.5,       # 30 minutes
        },
        "Ashley": {
            "location": "Bayview",
            "available_start": 17.25,  # 5:15 PM
            "available_end": 20.0,     # 8:00 PM
            "min_duration": 1.75,      # 105 minutes
        },
        "Ronald": {
            "location": "Chinatown",
            "available_start": 7.25,   # 7:15 AM
            "available_end": 14.75,    # 2:45 PM
            "min_duration": 1.5,       # 90 minutes
        },
        "William": {
            "location": "North Beach",
            "available_start": 13.25,  # 1:15 PM
            "available_end": 20.25,    # 8:15 PM
            "min_duration": 0.25,      # 15 minutes
        },
        "Daniel": {
            "location": "Mission District",
            "available_start": 7.0,    # 7:00 AM
            "available_end": 11.25,    # 11:15 AM
            "min_duration": 1.75,      # 105 minutes
        }
    }

    # Travel times dictionary (from -> to -> hours)
    travel_times = {
        "Presidio": {
            "Golden Gate Park": 12 / 60,
            "Bayview": 31 / 60,
            "Chinatown": 21 / 60,
            "North Beach": 18 / 60,
            "Mission District": 26 / 60,
        },
        "Golden Gate Park": {
            "Presidio": 11 / 60,
            "Bayview": 23 / 60,
            "Chinatown": 23 / 60,
            "North Beach": 24 / 60,
            "Mission District": 17 / 60,
        },
        "Bayview": {
            "Presidio": 31 / 60,
            "Golden Gate Park": 22 / 60,
            "Chinatown": 18 / 60,
            "North Beach": 21 / 60,
            "Mission District": 13 / 60,
        },
        "Chinatown": {
            "Presidio": 19 / 60,
            "Golden Gate Park": 23 / 60,
            "Bayview": 22 / 60,
            "North Beach": 3 / 60,
            "Mission District": 18 / 60,
        },
        "North Beach": {
            "Presidio": 17 / 60,
            "Golden Gate Park": 22 / 60,
            "Bayview": 22 / 60,
            "Chinatown": 6 / 60,
            "Mission District": 18 / 60,
        },
        "Mission District": {
            "Presidio": 25 / 60,
            "Golden Gate Park": 17 / 60,
            "Bayview": 15 / 60,
            "Chinatown": 16 / 60,
            "North Beach": 17 / 60,
        }
    }

    # Variables for each friend: start time, end time, and whether they are met
    variables = {}
    for name in friends:
        variables[name] = {
            "start": Real(f"{name}_start"),
            "end": Real(f"{name}_end"),
            "met": Bool(f"{name}_met")
        }

    # Current location starts at Presidio at 9:00 AM
    current_time = Real('current_time')
    s.add(current_time == 9.0)
    current_location = "Presidio"

    # Constraints for each friend
    for name in friends:
        friend = friends[name]
        var = variables[name]
        s.add(Implies(var["met"], var["start"] >= friend["available_start"]))
        s.add(Implies(var["met"], var["end"] <= friend["available_end"]))
        s.add(Implies(var["met"], var["end"] - var["start"] >= friend["min_duration"]))
        s.add(Implies(var["met"], var["start"] >= current_time + travel_times[current_location][friend["location"]]))

    # No overlapping meetings
    for name1 in friends:
        for name2 in friends:
            if name1 != name2:
                s.add(Implies(And(variables[name1]["met"], variables[name2]["met"]),
                             Or(variables[name1]["end"] <= variables[name2]["start"],
                                variables[name2]["end"] <= variables[name1]["start"])))

    # Maximize the number of friends met
    met_friends = [If(variables[name]["met"], 1, 0) for name in friends]
    total_met = sum(met_friends)
    s.maximize(total_met)

    # Check if a solution exists
    if s.check() == sat:
        model = s.model()
        result = {}
        for name in friends:
            if is_true(model.evaluate(variables[name]["met"])):
                start = model.evaluate(variables[name]["start"])
                end = model.evaluate(variables[name]["end"])
                result[name] = {
                    "start": float(start.numerator_as_long()) / float(start.denominator_as_long()),
                    "end": float(end.numerator_as_long()) / float(end.denominator_as_long()),
                    "location": friends[name]["location"]
                }
        return result
    else:
        return None

# Solve the problem
schedule = solve_scheduling()

# Print the solution
if schedule:
    print("SOLUTION:")
    for name in schedule:
        start = schedule[name]["start"]
        end = schedule[name]["end"]
        location = schedule[name]["location"]
        print(f"Meet {name} at {location} from {start:.2f} to {end:.2f}")
else:
    print("No feasible schedule found.")