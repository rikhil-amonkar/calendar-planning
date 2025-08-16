import json
from datetime import datetime, timedelta

# Input parameters
arrival_time = datetime.strptime("9:00", "%H:%M")
travel_times = {
    ("The Castro", "Mission District"): 7,
    ("The Castro", "Financial District"): 20,
    ("Mission District", "The Castro"): 7,
    ("Mission District", "Financial District"): 17,
    ("Financial District", "The Castro"): 23,
    ("Financial District", "Mission District"): 17
}
meetings = {
    "Laura": {"location": "Mission District", "start": datetime.strptime("12:15", "%H:%M"), "end": datetime.strptime("19:45", "%H:%M"), "min_duration": 75},
    "Anthony": {"location": "Financial District", "start": datetime.strptime("12:30", "%H:%M"), "end": datetime.strptime("14:45", "%H:%M"), "min_duration": 30}
}

def find_meeting_schedule(arrival_time, travel_times, meetings):
    def can_meet(meeting, current_time):
        meeting_start_time = max(current_time, meeting["start"])
        meeting_end_time = meeting_start_time + timedelta(minutes=meeting["min_duration"])
        return meeting_end_time <= meeting["end"]

    def add_meeting_to_itinerary(itinerary, person, location, start_time, end_time):
        itinerary.append({
            "action": "meet",
            "location": location,
            "person": person,
            "start_time": start_time.strftime("%H:%M"),
            "end_time": end_time.strftime("%H:%M")
        })

    def calculate_travel_time(current_location, next_location):
        return travel_times[(current_location, next_location)]

    def explore_schedule(current_time, current_location, itinerary, visited):
        if len(visited) == len(meetings):
            return itinerary

        best_itinerary = None
        for person, meeting in meetings.items():
            if person not in visited:
                travel_time = calculate_travel_time(current_location, meeting["location"])
                arrival_at_meeting = current_time + timedelta(minutes=travel_time)

                if can_meet(meeting, arrival_at_meeting):
                    meeting_start_time = max(arrival_at_meeting, meeting["start"])
                    meeting_end_time = meeting_start_time + timedelta(minutes=meeting["min_duration"])

                    new_itinerary = itinerary.copy()
                    add_meeting_to_itinerary(new_itinerary, person, meeting["location"], meeting_start_time, meeting_end_time)

                    # Check if we can return to The Castro after the meeting
                    return_time = meeting_end_time + timedelta(minutes=calculate_travel_time(meeting["location"], "The Castro"))
                    if return_time.hour < 18:
                        potential_itinerary = explore_schedule(meeting_end_time, meeting["location"], new_itinerary, visited | {person})
                        if potential_itinerary and (not best_itinerary or len(potential_itinerary) > len(best_itinerary)):
                            best_itinerary = potential_itinerary

        return best_itinerary

    initial_itinerary = []
    optimal_schedule = explore_schedule(arrival_time, "The Castro", initial_itinerary, set())
    return optimal_schedule if optimal_schedule else []

optimal_schedule = find_meeting_schedule(arrival_time, travel_times, meetings)
print(json.dumps(optimal_schedule, indent=2))