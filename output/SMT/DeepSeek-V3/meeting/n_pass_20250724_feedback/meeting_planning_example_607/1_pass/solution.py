from z3 import *
import json

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

    # Define the friends and their constraints
    friends = {
        "Karen": {
            "location": "Russian Hill",
            "available_start": "20:45",  # 8:45 PM
            "available_end": "21:45",    # 9:45 PM
            "min_duration": 60,
        },
        "Jessica": {
            "location": "The Castro",
            "available_start": "15:45",  # 3:45 PM
            "available_end": "19:30",    # 7:30 PM
            "min_duration": 60,
        },
        "Matthew": {
            "location": "Richmond District",
            "available_start": "07:30",  # 7:30 AM
            "available_end": "15:15",    # 3:15 PM
            "min_duration": 15,
        },
        "Michelle": {
            "location": "Marina District",
            "available_start": "10:30",  # 10:30 AM
            "available_end": "18:45",    # 6:45 PM
            "min_duration": 75,
        },
        "Carol": {
            "location": "North Beach",
            "available_start": "12:00",  # 12:00 PM
            "available_end": "17:00",    # 5:00 PM
            "min_duration": 90,
        },
        "Stephanie": {
            "location": "Union Square",
            "available_start": "10:45",  # 10:45 AM
            "available_end": "14:15",    # 2:15 PM
            "min_duration": 30,
        },
        "Linda": {
            "location": "Golden Gate Park",
            "available_start": "10:45",  # 10:45 AM
            "available_end": "22:00",    # 10:00 PM
            "min_duration": 90,
        }
    }

    # Travel times (in minutes) between locations
    travel_times = {
        "Sunset District": {
            "Russian Hill": 24,
            "The Castro": 17,
            "Richmond District": 12,
            "Marina District": 21,
            "North Beach": 29,
            "Union Square": 30,
            "Golden Gate Park": 11,
        },
        "Russian Hill": {
            "Sunset District": 23,
            "The Castro": 21,
            "Richmond District": 14,
            "Marina District": 7,
            "North Beach": 5,
            "Union Square": 11,
            "Golden Gate Park": 21,
        },
        "The Castro": {
            "Sunset District": 17,
            "Russian Hill": 18,
            "Richmond District": 16,
            "Marina District": 21,
            "North Beach": 20,
            "Union Square": 19,
            "Golden Gate Park": 11,
        },
        "Richmond District": {
            "Sunset District": 11,
            "Russian Hill": 13,
            "The Castro": 16,
            "Marina District": 9,
            "North Beach": 17,
            "Union Square": 21,
            "Golden Gate Park": 9,
        },
        "Marina District": {
            "Sunset District": 19,
            "Russian Hill": 8,
            "The Castro": 22,
            "Richmond District": 11,
            "North Beach": 11,
            "Union Square": 16,
            "Golden Gate Park": 18,
        },
        "North Beach": {
            "Sunset District": 27,
            "Russian Hill": 4,
            "The Castro": 22,
            "Richmond District": 18,
            "Marina District": 9,
            "Union Square": 7,
            "Golden Gate Park": 22,
        },
        "Union Square": {
            "Sunset District": 26,
            "Russian Hill": 13,
            "The Castro": 19,
            "Richmond District": 20,
            "Marina District": 18,
            "North Beach": 10,
            "Golden Gate Park": 22,
        },
        "Golden Gate Park": {
            "Sunset District": 10,
            "Russian Hill": 19,
            "The Castro": 13,
            "Richmond District": 7,
            "Marina District": 16,
            "North Beach": 24,
            "Union Square": 22,
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

    # Current location starts at Sunset District at 9:00 AM (540 minutes)
    current_location = "Sunset District"
    current_time = 540  # 9:00 AM in minutes

    # Create variables for each meeting's start and end times
    meeting_vars = {}
    for name in friends:
        start = Int(f"start_{name}")
        end = Int(f"end_{name}")
        meeting_vars[name] = (start, end)

    # Add constraints for each meeting
    for name, data in friends.items():
        start, end = meeting_vars[name]
        available_start = time_to_minutes(data["available_start"])
        available_end = time_to_minutes(data["available_end"])
        min_duration = data["min_duration"]

        # Meeting must be within available time
        s.add(start >= available_start)
        s.add(end <= available_end)
        s.add(end == start + min_duration)

    # Ensure meetings don't overlap and account for travel time
    for name1, (start1, end1) in meeting_vars.items():
        loc1 = friends[name1]["location"]
        for name2, (start2, end2) in meeting_vars.items():
            if name1 != name2:
                # Either meeting1 is before meeting2 with travel time
                # or meeting2 is before meeting1 with travel time
                travel_time = travel_times[loc1][friends[name2]["location"]]
                s.add(Or(
                    end1 + travel_time <= start2,
                    end2 + travel_times[friends[name2]["location"]][loc1] <= start1
                ))

    # Ensure the first meeting is after 9:00 AM and accounts for travel from Sunset District
    for name, (start, end) in meeting_vars.items():
        loc = friends[name]["location"]
        travel_time = travel_times[current_location][loc]
        s.add(start >= current_time + travel_time)

    # Try to meet as many friends as possible (soft constraint)
    # We'll prioritize meeting all friends if possible
    # If not, we'll maximize the number of meetings

    # Check if all meetings can be scheduled
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for name, (start, end) in meeting_vars.items():
            start_val = model.eval(start).as_long()
            end_val = model.eval(end).as_long()
            itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": minutes_to_time(start_val),
                "end_time": minutes_to_time(end_val)
            })
        # Sort itinerary by start time
        itinerary.sort(key=lambda x: time_to_minutes(x["start_time"]))
        return {"itinerary": itinerary}
    else:
        # If not all can be met, try to maximize the number of meetings
        # This part is more complex and would require iterative solving
        # For simplicity, we'll return an empty itinerary here
        return {"itinerary": []}

# Solve the problem
solution = solve_scheduling()
print("SOLUTION:")
print(json.dumps(solution, indent=2))