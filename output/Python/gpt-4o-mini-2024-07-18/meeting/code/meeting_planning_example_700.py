import json
from datetime import datetime, timedelta

# Travel distances between locations in minutes
travel_times = {
    "Presidio": {"Pacific Heights": 11, "Golden Gate Park": 12, "Fisherman's Wharf": 19, "Marina District": 11,
                 "Alamo Square": 19, "Sunset District": 15, "Nob Hill": 18, "North Beach": 18},
    "Pacific Heights": {"Presidio": 11, "Golden Gate Park": 15, "Fisherman's Wharf": 13, "Marina District": 6,
                        "Alamo Square": 10, "Sunset District": 21, "Nob Hill": 8, "North Beach": 9},
    "Golden Gate Park": {"Presidio": 11, "Pacific Heights": 16, "Fisherman's Wharf": 24, "Marina District": 18,
                         "Alamo Square": 9, "Sunset District": 10, "Nob Hill": 20, "North Beach": 23},
    "Fisherman's Wharf": {"Presidio": 17, "Pacific Heights": 12, "Golden Gate Park": 25, "Marina District": 9,
                          "Alamo Square": 21, "Sunset District": 27, "Nob Hill": 11, "North Beach": 6},
    "Marina District": {"Presidio": 10, "Pacific Heights": 7, "Golden Gate Park": 18, "Fisherman's Wharf": 10,
                        "Alamo Square": 15, "Sunset District": 19, "Nob Hill": 12, "North Beach": 11},
    "Alamo Square": {"Presidio": 17, "Pacific Heights": 10, "Golden Gate Park": 9, "Fisherman's Wharf": 19,
                     "Marina District": 15, "Sunset District": 16, "Nob Hill": 11, "North Beach": 15},
    "Sunset District": {"Presidio": 16, "Pacific Heights": 21, "Golden Gate Park": 11, "Fisherman's Wharf": 29,
                        "Marina District": 21, "Alamo Square": 17, "Nob Hill": 27, "North Beach": 28},
    "Nob Hill": {"Presidio": 17, "Pacific Heights": 8, "Golden Gate Park": 17, "Fisherman's Wharf": 10,
                  "Marina District": 11, "Alamo Square": 11, "Sunset District": 24, "North Beach": 8},
    "North Beach": {"Presidio": 17, "Pacific Heights": 8, "Golden Gate Park": 22, "Fisherman's Wharf": 5,
                    "Marina District": 9, "Alamo Square": 16, "Sunset District": 27, "Nob Hill": 7}
}

# Meeting constraints as input
meetings = {
    "Kevin": {"location": "Pacific Heights", "start": "7:15", "end": "8:45", "duration": 90},
    "Michelle": {"location": "Golden Gate Park", "start": "20:00", "end": "21:00", "duration": 15},
    "Emily": {"location": "Fisherman's Wharf", "start": "16:15", "end": "19:00", "duration": 30},
    "Mark": {"location": "Marina District", "start": "18:15", "end": "19:45", "duration": 75},
    "Barbara": {"location": "Alamo Square", "start": "17:00", "end": "19:00", "duration": 120},
    "Laura": {"location": "Sunset District", "start": "19:00", "end": "21:15", "duration": 75},
    "Mary": {"location": "Nob Hill", "start": "17:30", "end": "19:00", "duration": 45},
    "Helen": {"location": "North Beach", "start": "11:00", "end": "12:15", "duration": 45}
}

# Starting point and time
start_location = "Presidio"
start_time = datetime.strptime("09:00", "%H:%M")

# Function to check if a meeting can be scheduled
def can_schedule_meeting(meeting_start, meeting_end, required_duration, current_time, travel_time):
    available_time = (meeting_end - meeting_start).total_seconds() / 60
    return available_time >= required_duration + travel_time

def schedule_meetings():
    current_time = start_time
    itinerary = []

    # Meeting with Helen
    helen_start_time = datetime.strptime(meetings["Helen"]["start"], "%H:%M")
    helen_end_time = datetime.strptime(meetings["Helen"]["end"], "%H:%M")
    travel_time_to_helen = travel_times[start_location][meetings["Helen"]["location"]]
    
    if current_time <= helen_start_time and can_schedule_meeting(helen_start_time, helen_end_time, meetings["Helen"]["duration"], current_time, travel_time_to_helen):
        meeting_start = helen_start_time
        meeting_end = meeting_start + timedelta(minutes=meetings["Helen"]["duration"])
        itinerary.append({"action": "meet", "location": meetings["Helen"]["location"], "person": "Helen", "start_time": meeting_start.strftime("%H:%M"), "end_time": meeting_end.strftime("%H:%M")})
        current_time = meeting_end + timedelta(minutes=travel_time_to_helen)

    # Meeting with Kevin
    kevin_start_time = datetime.strptime(meetings["Kevin"]["start"], "%H:%M")
    kevin_end_time = datetime.strptime(meetings["Kevin"]["end"], "%H:%M")
    travel_time_to_kevin = travel_times[start_location][meetings["Kevin"]["location"]]
    
    if current_time < kevin_start_time:
        current_time = kevin_start_time

    if can_schedule_meeting(kevin_start_time, kevin_end_time, meetings["Kevin"]["duration"], current_time, travel_time_to_kevin):
        meeting_start = current_time
        meeting_end = meeting_start + timedelta(minutes=meetings["Kevin"]["duration"])
        itinerary.append({"action": "meet", "location": meetings["Kevin"]["location"], "person": "Kevin", "start_time": meeting_start.strftime("%H:%M"), "end_time": meeting_end.strftime("%H:%M")})
        current_time = meeting_end + timedelta(minutes=travel_time_to_kevin)

    # Meeting with Emily
    emily_start_time = datetime.strptime(meetings["Emily"]["start"], "%H:%M")
    emily_end_time = datetime.strptime(meetings["Emily"]["end"], "%H:%M")
    travel_time_to_emily = travel_times[start_location][meetings["Emily"]["location"]]
    
    current_time = max(current_time, emily_start_time)
    
    if can_schedule_meeting(emily_start_time, emily_end_time, meetings["Emily"]["duration"], current_time, travel_time_to_emily):
        meeting_start = current_time
        meeting_end = meeting_start + timedelta(minutes=meetings["Emily"]["duration"])
        itinerary.append({"action": "meet", "location": meetings["Emily"]["location"], "person": "Emily", "start_time": meeting_start.strftime("%H:%M"), "end_time": meeting_end.strftime("%H:%M")})
        current_time = meeting_end + timedelta(minutes=travel_time_to_emily)
    
    # Meeting with Mark
    mark_start_time = datetime.strptime(meetings["Mark"]["start"], "%H:%M")
    mark_end_time = datetime.strptime(meetings["Mark"]["end"], "%H:%M")
    travel_time_to_mark = travel_times[start_location][meetings["Mark"]["location"]]
    
    current_time = max(current_time, mark_start_time)
    
    if can_schedule_meeting(mark_start_time, mark_end_time, meetings["Mark"]["duration"], current_time, travel_time_to_mark):
        meeting_start = current_time
        meeting_end = meeting_start + timedelta(minutes=meetings["Mark"]["duration"])
        itinerary.append({"action": "meet", "location": meetings["Mark"]["location"], "person": "Mark", "start_time": meeting_start.strftime("%H:%M"), "end_time": meeting_end.strftime("%H:%M")})
        current_time = meeting_end + timedelta(minutes=travel_time_to_mark)

    # Meeting with Barbara
    barbara_start_time = datetime.strptime(meetings["Barbara"]["start"], "%H:%M")
    barbara_end_time = datetime.strptime(meetings["Barbara"]["end"], "%H:%M")
    travel_time_to_barbara = travel_times[start_location][meetings["Barbara"]["location"]]
    
    current_time = max(current_time, barbara_start_time)
    
    if can_schedule_meeting(barbara_start_time, barbara_end_time, meetings["Barbara"]["duration"], current_time, travel_time_to_barbara):
        meeting_start = current_time
        meeting_end = meeting_start + timedelta(minutes=meetings["Barbara"]["duration"])
        itinerary.append({"action": "meet", "location": meetings["Barbara"]["location"], "person": "Barbara", "start_time": meeting_start.strftime("%H:%M"), "end_time": meeting_end.strftime("%H:%M")})
        current_time = meeting_end + timedelta(minutes=travel_time_to_barbara)

    # Meeting with Mary
    mary_start_time = datetime.strptime(meetings["Mary"]["start"], "%H:%M")
    mary_end_time = datetime.strptime(meetings["Mary"]["end"], "%H:%M")
    travel_time_to_mary = travel_times[start_location][meetings["Mary"]["location"]]

    current_time = max(current_time, mary_start_time)

    if can_schedule_meeting(mary_start_time, mary_end_time, meetings["Mary"]["duration"], current_time, travel_time_to_mary):
        meeting_start = current_time
        meeting_end = meeting_start + timedelta(minutes=meetings["Mary"]["duration"])
        itinerary.append({"action": "meet", "location": meetings["Mary"]["location"], "person": "Mary", "start_time": meeting_start.strftime("%H:%M"), "end_time": meeting_end.strftime("%H:%M")})
        current_time = meeting_end + timedelta(minutes=travel_time_to_mary)

    # Meeting with Laura
    laura_start_time = datetime.strptime(meetings["Laura"]["start"], "%H:%M")
    laura_end_time = datetime.strptime(meetings["Laura"]["end"], "%H:%M")
    travel_time_to_laura = travel_times[start_location][meetings["Laura"]["location"]]

    current_time = max(current_time, laura_start_time)

    if can_schedule_meeting(laura_start_time, laura_end_time, meetings["Laura"]["duration"], current_time, travel_time_to_laura):
        meeting_start = current_time
        meeting_end = meeting_start + timedelta(minutes=meetings["Laura"]["duration"])
        itinerary.append({"action": "meet", "location": meetings["Laura"]["location"], "person": "Laura", "start_time": meeting_start.strftime("%H:%M"), "end_time": meeting_end.strftime("%H:%M")})

    # Meeting with Michelle
    michelle_start_time = datetime.strptime(meetings["Michelle"]["start"], "%H:%M")
    michelle_end_time = datetime.strptime(meetings["Michelle"]["end"], "%H:%M")
    travel_time_to_michelle = travel_times[start_location][meetings["Michelle"]["location"]]

    current_time = max(current_time, michelle_start_time)

    if can_schedule_meeting(michelle_start_time, michelle_end_time, meetings["Michelle"]["duration"], current_time, travel_time_to_michelle):
        meeting_start = current_time
        meeting_end = meeting_start + timedelta(minutes=meetings["Michelle"]["duration"])
        itinerary.append({"action": "meet", "location": meetings["Michelle"]["location"], "person": "Michelle", "start_time": meeting_start.strftime("%H:%M"), "end_time": meeting_end.strftime("%H:%M")})

    return {"itinerary": itinerary}

if __name__ == "__main__":
    schedule = schedule_meetings()
    print(json.dumps(schedule, indent=2))