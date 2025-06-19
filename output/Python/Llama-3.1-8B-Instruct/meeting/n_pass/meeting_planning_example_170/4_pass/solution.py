import json
import datetime

def compute_travel_time(origin, destination, travel_times):
    return travel_times[f"{origin} to {destination}"]

def compute_meeting_schedule(arrival_time, emily_time, margaret_time, travel_times):
    # Convert time strings to datetime objects
    arrival_time = datetime.datetime.strptime(arrival_time, "%H:%M")
    emily_time = [datetime.datetime.strptime(t, "%H:%M") for t in emily_time]
    margaret_time = [datetime.datetime.strptime(t, "%H:%M") for t in margaret_time]

    # Compute travel times
    north_beach_to_union_square = compute_travel_time("North Beach", "Union Square", travel_times)
    north_beach_to_russian_hill = compute_travel_time("North Beach", "Russian Hill", travel_times)
    union_square_to_north_beach = compute_travel_time("Union Square", "North Beach", travel_times)
    union_square_to_russian_hill = compute_travel_time("Union Square", "Russian Hill", travel_times)
    russian_hill_to_north_beach = compute_travel_time("Russian Hill", "North Beach", travel_times)
    russian_hill_to_union_square = compute_travel_time("Russian Hill", "Union Square", travel_times)

    # Initialize schedule
    schedule = []

    # Meet Emily
    for emily_start in emily_time:
        if arrival_time < emily_start:
            emily_start_time = emily_start - datetime.timedelta(minutes=north_beach_to_union_square)
            emily_end_time = emily_start_time + datetime.timedelta(minutes=45)
            if emily_start_time < emily_start and emily_end_time < emily_start:
                # If the meeting time with Emily is outside her availability, skip it
                continue
            schedule.append({
                "action": "meet",
                "location": "Union Square",
                "person": "Emily",
                "start_time": emily_start_time.strftime("%H:%M"),
                "end_time": emily_end_time.strftime("%H:%M")
            })
            break

    # Travel to Russian Hill
    if schedule:
        emily_end_time = schedule[-1]['end_time']
        emily_end_time = datetime.datetime.strptime(emily_end_time, "%H:%M")
        russian_hill_arrival_time = emily_end_time + datetime.timedelta(minutes=north_beach_to_russian_hill)
        schedule.append({
            "action": "travel",
            "location": "Russian Hill",
            "person": "",
            "start_time": emily_end_time.strftime("%H:%M"),
            "end_time": russian_hill_arrival_time.strftime("%H:%M")
        })

    # Meet Margaret
    if schedule:
        margaret_start_time = max(margaret_time[0], russian_hill_arrival_time)
        margaret_end_time = margaret_start_time + datetime.timedelta(minutes=120)
        schedule.append({
            "action": "meet",
            "location": "Russian Hill",
            "person": "Margaret",
            "start_time": margaret_start_time.strftime("%H:%M"),
            "end_time": margaret_end_time.strftime("%H:%M")
        })

    # Check if meeting time with Emily is outside her availability
    if schedule and emily_time[0] < datetime.datetime.strptime(schedule[-1]['start_time'], "%H:%M"):
        print("Warning: Meeting time with Emily is outside her availability.")

    return schedule

def main():
    travel_times = {
        "North Beach to Union Square": 7,
        "North Beach to Russian Hill": 4,
        "Union Square to North Beach": 10,
        "Union Square to Russian Hill": 13,
        "Russian Hill to North Beach": 5,
        "Russian Hill to Union Square": 11
    }
    arrival_time = "09:00"
    emily_time = ["16:00", "17:15"]
    margaret_time = ["19:00", "21:00"]
    schedule = compute_meeting_schedule(arrival_time, emily_time, margaret_time, travel_times)
    print(json.dumps({"itinerary": schedule}, indent=4))

if __name__ == "__main__":
    main()