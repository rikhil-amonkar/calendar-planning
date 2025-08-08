from z3 import *
import json

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

    # Define the friends and their constraints
    friends = {
        "Karen": {
            "location": "Russian Hill",
            "available_start": (20, 45),  # 8:45 PM as 20:45
            "available_end": (21, 45),    # 9:45 PM as 21:45
            "min_duration": 60             # minutes
        },
        "Jessica": {
            "location": "The Castro",
            "available_start": (15, 45),   # 3:45 PM as 15:45
            "available_end": (19, 30),     # 7:30 PM as 19:30
            "min_duration": 60
        },
        "Matthew": {
            "location": "Richmond District",
            "available_start": (7, 30),    # 7:30 AM as 7:30
            "available_end": (15, 15),     # 3:15 PM as 15:15
            "min_duration": 15
        },
        "Michelle": {
            "location": "Marina District",
            "available_start": (10, 30),   # 10:30 AM as 10:30
            "available_end": (18, 45),     # 6:45 PM as 18:45
            "min_duration": 75
        },
        "Carol": {
            "location": "North Beach",
            "available_start": (12, 0),    # 12:00 PM as 12:00
            "available_end": (17, 0),      # 5:00 PM as 17:00
            "min_duration": 90
        },
        "Stephanie": {
            "location": "Union Square",
            "available_start": (10, 45),   # 10:45 AM as 10:45
            "available_end": (14, 15),     # 2:15 PM as 14:15
            "min_duration": 30
        },
        "Linda": {
            "location": "Golden Gate Park",
            "available_start": (10, 45),   # 10:45 AM as 10:45
            "available_end": (22, 0),      # 10:00 PM as 22:00
            "min_duration": 90
        }
    }

    # Travel times dictionary: from_location -> to_location -> minutes
    travel_times = {
        "Sunset District": {
            "Russian Hill": 24,
            "The Castro": 17,
            "Richmond District": 12,
            "Marina District": 21,
            "North Beach": 29,
            "Union Square": 30,
            "Golden Gate Park": 11
        },
        "Russian Hill": {
            "Sunset District": 23,
            "The Castro": 21,
            "Richmond District": 14,
            "Marina District": 7,
            "North Beach": 5,
            "Union Square": 11,
            "Golden Gate Park": 21
        },
        "The Castro": {
            "Sunset District": 17,
            "Russian Hill": 18,
            "Richmond District": 16,
            "Marina District": 21,
            "North Beach": 20,
            "Union Square": 19,
            "Golden Gate Park": 11
        },
        "Richmond District": {
            "Sunset District": 11,
            "Russian Hill": 13,
            "The Castro": 16,
            "Marina District": 9,
            "North Beach": 17,
            "Union Square": 21,
            "Golden Gate Park": 9
        },
        "Marina District": {
            "Sunset District": 19,
            "Russian Hill": 8,
            "The Castro": 22,
            "Richmond District": 11,
            "North Beach": 11,
            "Union Square": 16,
            "Golden Gate Park": 18
        },
        "North Beach": {
            "Sunset District": 27,
            "Russian Hill": 4,
            "The Castro": 22,
            "Richmond District": 18,
            "Marina District": 9,
            "Union Square": 7,
            "Golden Gate Park": 22
        },
        "Union Square": {
            "Sunset District": 26,
            "Russian Hill": 13,
            "The Castro": 19,
            "Richmond District": 20,
            "Marina District": 18,
            "North Beach": 10,
            "Golden Gate Park": 22
        },
        "Golden Gate Park": {
            "Sunset District": 10,
            "Russian Hill": 19,
            "The Castro": 13,
            "Richmond District": 7,
            "Marina District": 16,
            "North Beach": 24,
            "Union Square": 22
        }
    }

    # Convert available times to minutes since 9:00 AM (540 minutes)
    def time_to_minutes(hour, minute):
        return hour * 60 + minute

    # Current location starts at Sunset District at 9:00 AM (540 minutes)
    current_time = 540  # 9:00 AM in minutes
    current_location = "Sunset District"

    # Create variables for each friend's meeting start and end times
    meeting_vars = {}
    for name in friends:
        start = Int(f'start_{name}')
        end = Int(f'end_{name}')
        available_start = time_to_minutes(*friends[name]["available_start"])
        available_end = time_to_minutes(*friends[name]["available_end"])
        min_duration = friends[name]["min_duration"]

        # Constraints: start and end within available window
        s.add(start >= available_start)
        s.add(end <= available_end)
        s.add(end == start + min_duration)
        meeting_vars[name] = {
            "start": start,
            "end": end,
            "location": friends[name]["location"]
        }

    # Define the order of meetings. We'll let Z3 determine the order by adding sequencing constraints.
    # We need to ensure that for any two meetings, one is before the other with travel time in between.
    # However, with many friends, this approach can be complex. Instead, we can model the problem as a sequence.

    # To simplify, we'll assume that the meetings can be ordered in any way, and we'll add constraints
    # that for any two meetings A and B, if A is before B, then B's start >= A's end + travel time from A's location to B's location.

    # But this is computationally expensive for Z3. Instead, we can impose a total order (permutation) of meetings.
    # Here, we'll use a list of all possible meeting orders and let Z3 choose one.

    # However, for the sake of this problem, we'll proceed by manually choosing a plausible order based on locations and times,
    # but in the code, we'll let Z3 handle the sequencing by adding constraints between all pairs of meetings.

    # Collect all names
    names = list(friends.keys())

    # For each pair of distinct meetings, add constraints that they are either before or after each other with travel time.
    for i in range(len(names)):
        for j in range(i+1, len(names)):
            name1 = names[i]
            name2 = names[j]
            loc1 = meeting_vars[name1]["location"]
            loc2 = meeting_vars[name2]["location"]
            travel = travel_times[loc1][loc2]

            # Either meeting1 is before meeting2 or vice versa
            before = And(
                meeting_vars[name1]["end"] + travel <= meeting_vars[name2]["start"]
            )
            after = And(
                meeting_vars[name2]["end"] + travel_times[loc2][loc1] <= meeting_vars[name1]["start"]
            )
            s.add(Or(before, after))

    # Also, all meetings must start after the initial time (9:00 AM) plus travel time from Sunset District.
    for name in names:
        loc = meeting_vars[name]["location"]
        travel = travel_times[current_location][loc]
        s.add(meeting_vars[name]["start"] >= current_time + travel)

    # Check if the constraints are satisfiable
    if s.check() == sat:
        model = s.model()
        itinerary = []
        # Collect all meetings with their start and end times
        meetings = []
        for name in names:
            start_val = model[meeting_vars[name]["start"]].as_long()
            end_val = model[meeting_vars[name]["end"]].as_long()
            meetings.append({
                "name": name,
                "start": start_val,
                "end": end_val,
                "location": meeting_vars[name]["location"]
            })

        # Sort meetings by start time
        meetings.sort(key=lambda x: x["start"])

        # Convert start and end times from minutes to HH:MM format
        def minutes_to_time(minutes):
            hours = minutes // 60
            mins = minutes % 60
            return f"{hours:02d}:{mins:02d}"

        for meeting in meetings:
            itinerary.append({
                "action": "meet",
                "person": meeting["name"],
                "start_time": minutes_to_time(meeting["start"]),
                "end_time": minutes_to_time(meeting["end"])
            })

        # Prepare the output
        output = {
            "itinerary": itinerary
        }
        print(json.dumps(output, indent=2))
    else:
        print('{"itinerary": []}')

solve_scheduling()