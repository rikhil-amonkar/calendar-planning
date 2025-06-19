import json
import datetime

def calculate_travel_time(start_location, end_location, travel_times):
    if start_location == end_location:
        return 0
    return travel_times.get(f"{start_location}-{end_location}", travel_times.get(f"{end_location}-{start_location}", 0))

def generate_itinerary(arrival_time, departure_time, locations, travel_times, constraints):
    itinerary = []
    current_time = datetime.datetime.strptime(arrival_time, "%H:%M")
    for person, availability in constraints.items():
        for time_range in availability:
            start_time = datetime.datetime.strptime(time_range[0], "%H:%M")
            end_time = datetime.datetime.strptime(time_range[1], "%H:%M")
            if (current_time >= start_time and current_time < end_time) or (current_time < start_time and (end_time - current_time).total_seconds() / 60 >= 90):
                meeting_start_time = max(current_time, start_time)
                meeting_end_time = min(end_time, meeting_start_time + datetime.timedelta(minutes=90))
                meeting_location = "Fisherman's Wharf" if meeting_start_time.hour < 14 else "Nob Hill"
                itinerary.append({
                    "action": "meet",
                    "location": meeting_location,
                    "person": person,
                    "start_time": meeting_start_time.strftime("%H:%M"),
                    "end_time": meeting_end_time.strftime("%H:%M")
                })
                current_time = meeting_end_time + datetime.timedelta(minutes=calculate_travel_time(meeting_location, "Fisherman's Wharf" if meeting_start_time.hour < 14 else "Nob Hill", travel_times))
    return itinerary

def main():
    travel_times = {
        "Fisherman's Wharf-Nob Hill": 11,
        "Nob Hill-Fisherman's Wharf": 11
    }
    constraints = {
        "Kenneth": [("14:15", "19:45")]
    }
    arrival_time = "09:00"
    departure_time = "23:59"
    locations = ["Fisherman's Wharf", "Nob Hill"]
    itinerary = generate_itinerary(arrival_time, departure_time, locations, travel_times, constraints)
    print(json.dumps({"itinerary": itinerary}, indent=4))

if __name__ == "__main__":
    main()