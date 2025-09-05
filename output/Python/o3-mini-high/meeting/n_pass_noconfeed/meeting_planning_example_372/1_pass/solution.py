import itertools
import json

def format_time(minutes):
    hour = minutes // 60
    minute = minutes % 60
    # Format as H:MM (no leading zero for hour)
    return f"{hour}:{minute:02d}"

def main():
    # Define travel times (in minutes) between locations.
    travel_times = {
        ("Sunset District", "Alamo Square"): 17,
        ("Sunset District", "Russian Hill"): 24,
        ("Sunset District", "Golden Gate Park"): 11,
        ("Sunset District", "Mission District"): 24,
        ("Alamo Square", "Sunset District"): 16,
        ("Alamo Square", "Russian Hill"): 13,
        ("Alamo Square", "Golden Gate Park"): 9,
        ("Alamo Square", "Mission District"): 10,
        ("Russian Hill", "Sunset District"): 23,
        ("Russian Hill", "Alamo Square"): 15,
        ("Russian Hill", "Golden Gate Park"): 21,
        ("Russian Hill", "Mission District"): 16,
        ("Golden Gate Park", "Sunset District"): 10,
        ("Golden Gate Park", "Alamo Square"): 10,
        ("Golden Gate Park", "Russian Hill"): 19,
        ("Golden Gate Park", "Mission District"): 17,
        ("Mission District", "Sunset District"): 24,
        ("Mission District", "Alamo Square"): 11,
        ("Mission District", "Russian Hill"): 15,
        ("Mission District", "Golden Gate Park"): 17
    }
    
    # Define meeting events along with constraints.
    # Times are in minutes from midnight.
    events = [
        {
            "person": "Charles",
            "location": "Alamo Square",
            "avail_start": 18 * 60,       # 18:00 = 1080 minutes
            "avail_end": 20 * 60 + 45,      # 20:45 = 1245 minutes
            "duration": 90
        },
        {
            "person": "Margaret",
            "location": "Russian Hill",
            "avail_start": 9 * 60,        # 9:00 = 540 minutes
            "avail_end": 16 * 60,         # 16:00 = 960 minutes
            "duration": 30
        },
        {
            "person": "Daniel",
            "location": "Golden Gate Park",
            "avail_start": 8 * 60,        # 8:00 = 480 minutes
            "avail_end": 13 * 60 + 30,      # 13:30 = 810 minutes
            "duration": 15
        },
        {
            "person": "Stephanie",
            "location": "Mission District",
            "avail_start": 20 * 60 + 30,    # 20:30 = 1230 minutes
            "avail_end": 22 * 60,         # 22:00 = 1320 minutes
            "duration": 90
        }
    ]
    
    # Starting parameters.
    start_location = "Sunset District"
    start_time = 9 * 60  # 9:00 AM = 540 minutes

    best_schedule = None
    best_count = 0
    best_finish = float('inf')
    best_total_wait = float('inf')

    # We try all permutations of the events.
    for perm in itertools.permutations(events, len(events)):
        current_time = start_time
        current_location = start_location
        schedule = []
        total_wait = 0
        feasible = True
        # Process each event in the permutation
        for event in perm:
            travel = travel_times.get((current_location, event["location"]), None)
            if travel is None:
                feasible = False
                break
            arrival = current_time + travel
            # The meeting can't start before the friend's available time.
            meeting_start = max(arrival, event["avail_start"])
            wait = meeting_start - arrival
            meeting_end = meeting_start + event["duration"]
            # Ensure the meeting finishes before the friend's available end time.
            if meeting_end > event["avail_end"]:
                feasible = False
                break
            schedule.append({
                "action": "meet",
                "location": event["location"],
                "person": event["person"],
                "start_time": format_time(meeting_start),
                "end_time": format_time(meeting_end)
            })
            total_wait += wait
            current_time = meeting_end
            current_location = event["location"]
        if feasible:
            count = len(schedule)
            finish_time = current_time
            # Our objective: maximize number of meetings, then minimize finish time, then minimize total waiting.
            if (count > best_count or 
                (count == best_count and finish_time < best_finish) or
                (count == best_count and finish_time == best_finish and total_wait < best_total_wait)):
                best_schedule = schedule
                best_count = count
                best_finish = finish_time
                best_total_wait = total_wait

    # If no schedule with all events is feasible, we try subsets descending in size.
    if best_schedule is None:
        for r in range(len(events), 0, -1):
            for perm in itertools.permutations(events, r):
                current_time = start_time
                current_location = start_location
                schedule = []
                total_wait = 0
                feasible = True
                for event in perm:
                    travel = travel_times.get((current_location, event["location"]), None)
                    if travel is None:
                        feasible = False
                        break
                    arrival = current_time + travel
                    meeting_start = max(arrival, event["avail_start"])
                    wait = meeting_start - arrival
                    meeting_end = meeting_start + event["duration"]
                    if meeting_end > event["avail_end"]:
                        feasible = False
                        break
                    schedule.append({
                        "action": "meet",
                        "location": event["location"],
                        "person": event["person"],
                        "start_time": format_time(meeting_start),
                        "end_time": format_time(meeting_end)
                    })
                    total_wait += wait
                    current_time = meeting_end
                    current_location = event["location"]
                if feasible and len(schedule) > best_count:
                    best_schedule = schedule
                    best_count = len(schedule)
                    best_finish = current_time
                    best_total_wait = total_wait
            if best_schedule is not None:
                break

    output = {"itinerary": best_schedule if best_schedule is not None else []}
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()