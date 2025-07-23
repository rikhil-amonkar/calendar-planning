import json
from itertools import permutations

def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def calculate_schedule():
    # Travel times in minutes
    travel_times = {
        ('Union Square', 'Mission District'): 14,
        ('Union Square', 'Bayview'): 15,
        ('Union Square', 'Sunset District'): 26,
        ('Mission District', 'Union Square'): 15,
        ('Mission District', 'Bayview'): 15,
        ('Mission District', 'Sunset District'): 24,
        ('Bayview', 'Union Square'): 17,
        ('Bayview', 'Mission District'): 13,
        ('Bayview', 'Sunset District'): 23,
        ('Sunset District', 'Union Square'): 30,
        ('Sunset District', 'Mission District'): 24,
        ('Sunset District', 'Bayview'): 22,
    }

    # Constraints
    arrival_time = time_to_minutes("9:00")
    friends = [
        {
            "name": "Rebecca",
            "location": "Mission District",
            "available_start": time_to_minutes("11:30"),
            "available_end": time_to_minutes("20:15"),
            "duration": 120
        },
        {
            "name": "Karen",
            "location": "Bayview",
            "available_start": time_to_minutes("12:45"),
            "available_end": time_to_minutes("15:00"),
            "duration": 120
        },
        {
            "name": "Carol",
            "location": "Sunset District",
            "available_start": time_to_minutes("10:15"),
            "available_end": time_to_minutes("11:45"),
            "duration": 30
        }
    ]

    best_schedule = None
    max_meetings = 0

    # Try all permutations of meeting orders
    for order in permutations(friends):
        current_location = "Union Square"
        current_time = arrival_time
        schedule = []
        meetings_count = 0

        for friend in order:
            # Travel to friend's location
            travel_key = (current_location, friend["location"])
            travel_time = travel_times.get(travel_key, 0)
            arrival_at_friend = current_time + travel_time

            # Check if we can meet the friend
            meeting_start = max(arrival_at_friend, friend["available_start"])
            meeting_end = meeting_start + friend["duration"]

            if meeting_end <= friend["available_end"]:
                schedule.append({
                    "action": "meet",
                    "location": friend["location"],
                    "person": friend["name"],
                    "start_time": minutes_to_time(meeting_start),
                    "end_time": minutes_to_time(meeting_end)
                })
                current_location = friend["location"]
                current_time = meeting_end
                meetings_count += 1
            else:
                # Can't meet this friend in this order
                break

        if meetings_count > max_meetings:
            max_meetings = meetings_count
            best_schedule = schedule
        elif meetings_count == max_meetings and meetings_count > 0:
            # Prefer schedules that end earlier
            if not best_schedule or current_time < time_to_minutes(best_schedule[-1]["end_time"]):
                best_schedule = schedule

    if not best_schedule:
        best_schedule = []

    return {"itinerary": best_schedule}

if __name__ == "__main__":
    schedule = calculate_schedule()
    print(json.dumps(schedule, indent=2))