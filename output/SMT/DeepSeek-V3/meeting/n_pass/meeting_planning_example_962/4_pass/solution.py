import json
from z3 import *

def solve_scheduling_problem():
    solver = Optimize()

    # Define friends and their constraints
    friends = [
        {"name": "Elizabeth", "location": "Marina District", "available_start": "19:00", "available_end": "20:45", "min_duration": 105},
        {"name": "Joshua", "location": "Presidio", "available_start": "8:30", "available_end": "13:15", "min_duration": 105},
        {"name": "Timothy", "location": "North Beach", "available_start": "19:45", "available_end": "22:00", "min_duration": 90},
        {"name": "David", "location": "Embarcadero", "available_start": "10:45", "available_end": "12:30", "min_duration": 30},
        {"name": "Kimberly", "location": "Haight-Ashbury", "available_start": "16:45", "available_end": "21:30", "min_duration": 75},
        {"name": "Lisa", "location": "Golden Gate Park", "available_start": "17:30", "available_end": "21:45", "min_duration": 45},
        {"name": "Ronald", "location": "Richmond District", "available_start": "8:00", "available_end": "9:30", "min_duration": 90},
        {"name": "Stephanie", "location": "Alamo Square", "available_start": "15:30", "available_end": "16:30", "min_duration": 30},
        {"name": "Helen", "location": "Financial District", "available_start": "17:30", "available_end": "18:30", "min_duration": 45},
        {"name": "Laura", "location": "Sunset District", "available_start": "17:45", "available_end": "21:15", "min_duration": 90}
    ]

    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    current_time = time_to_minutes("9:00")

    meetings = []
    for friend in friends:
        available_start = time_to_minutes(friend["available_start"])
        available_end = time_to_minutes(friend["available_end"])
        min_duration = friend["min_duration"]

        start = Int(f'start_{friend["name"]}')
        end = Int(f'end_{friend["name"]}')
        meet = Bool(f'meet_{friend["name"]}')

        solver.add(Implies(meet, start >= available_start))
        solver.add(Implies(meet, end <= available_end))
        solver.add(Implies(meet, end == start + min_duration))
        solver.add(Implies(meet, start + min_duration <= available_end))

        meetings.append({
            "name": friend["name"],
            "location": friend["location"],
            "start": start,
            "end": end,
            "meet": meet,
            "min_duration": min_duration
        })

    travel_times = {
        ("The Castro", "Richmond District"): 16,
        ("Richmond District", "Presidio"): 7,
        ("Presidio", "Embarcadero"): 20,
        ("Embarcadero", "Alamo Square"): 19,
        ("Alamo Square", "Financial District"): 17,
        ("Financial District", "Haight-Ashbury"): 19,
        ("Haight-Ashbury", "Golden Gate Park"): 7,
        ("Golden Gate Park", "Sunset District"): 10,
        ("Sunset District", "Marina District"): 21,
        ("Marina District", "North Beach"): 11
    }

    # Define meeting order with travel times
    order = [
        ("Ronald", "Richmond District"),
        ("Joshua", "Presidio"),
        ("David", "Embarcadero"),
        ("Stephanie", "Alamo Square"),
        ("Helen", "Financial District"),
        ("Kimberly", "Haight-Ashbury"),
        ("Lisa", "Golden Gate Park"),
        ("Laura", "Sunset District"),
        ("Elizabeth", "Marina District"),
        ("Timothy", "North Beach")
    ]

    prev_end = Int('prev_end')
    solver.add(prev_end == current_time)
    prev_location = "The Castro"
    scheduled_meetings = []

    for person, location in order:
        friend = next(f for f in meetings if f["name"] == person)
        meet = friend["meet"]
        start = friend["start"]
        end = friend["end"]
        min_duration = friend["min_duration"]

        travel_time = travel_times.get((prev_location, location), 0)
        solver.add(Implies(meet, start >= prev_end + travel_time))

        scheduled_meetings.append(meet)
        new_prev_end = If(meet, end, prev_end)
        new_prev_location = If(meet, location, prev_location)

        prev_end = new_prev_end
        prev_location = new_prev_location

    solver.maximize(Sum([If(m, 1, 0) for m in scheduled_meetings]))

    if solver.check() == sat:
        model = solver.model()
        itinerary = []

        for friend in meetings:
            if is_true(model[friend["meet"]]):
                start_min = model[friend["start"]].as_long()
                end_min = model[friend["end"]].as_long()
                start_time = f"{start_min // 60:02d}:{start_min % 60:02d}"
                end_time = f"{end_min // 60:02d}:{end_min % 60:02d}"
                itinerary.append({
                    "action": "meet",
                    "person": friend["name"],
                    "start_time": start_time,
                    "end_time": end_time
                })

        itinerary.sort(key=lambda x: time_to_minutes(x["start_time"]))
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

solution = solve_scheduling_problem()
print(json.dumps(solution, indent=2))