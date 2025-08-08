#!/usr/bin/env python3
import json

def minutes_to_time(m):
    hour = m // 60
    minute = m % 60
    return f"{hour}:{minute:02d}"

def compute_schedule(meetings, start_location, start_time, travel_times):
    itinerary = []
    current_time = start_time
    current_location = start_location
    for meeting in meetings:
        # Determine travel time from current location to the meeting location.
        travel_time = travel_times.get(current_location, {}).get(meeting["location"])
        if travel_time is None:
            # Fall back on symmetric lookup if needed.
            travel_time = travel_times.get(meeting["location"], {}).get(current_location, 0)
        # Travel to next meeting.
        current_time += travel_time
        # Wait if arriving before the friend’s available time.
        meeting_start = max(current_time, meeting["available_start"])
        meeting_end = meeting_start + meeting["duration"]
        # Ensure the meeting fits within the friend’s available window.
        if meeting_end > meeting["available_end"]:
            return None  # Infeasible schedule.
        itinerary.append({
            "action": "meet",
            "location": meeting["location"],
            "person": meeting["person"],
            "start_time": minutes_to_time(meeting_start),
            "end_time": minutes_to_time(meeting_end)
        })
        current_time = meeting_end
        current_location = meeting["location"]
    return itinerary, current_time

def main():
    # Travel distances (in minutes) between locations.
    travel_times = {
        "The Castro": {
            "Alamo Square": 8,
            "Richmond District": 16,
            "Financial District": 21,
            "Union Square": 19,
            "Fisherman's Wharf": 24,
            "Marina District": 21,
            "Haight-Ashbury": 6,
            "Mission District": 7,
            "Pacific Heights": 16,
            "Golden Gate Park": 11
        },
        "Alamo Square": {
            "The Castro": 8,
            "Richmond District": 11,
            "Financial District": 17,
            "Union Square": 14,
            "Fisherman's Wharf": 19,
            "Marina District": 15,
            "Haight-Ashbury": 5,
            "Mission District": 10,
            "Pacific Heights": 10,
            "Golden Gate Park": 9
        },
        "Richmond District": {
            "The Castro": 16,
            "Alamo Square": 13,
            "Financial District": 22,
            "Union Square": 21,
            "Fisherman's Wharf": 18,
            "Marina District": 9,
            "Haight-Ashbury": 10,
            "Mission District": 20,
            "Pacific Heights": 10,
            "Golden Gate Park": 9
        },
        "Financial District": {
            "The Castro": 20,
            "Alamo Square": 17,
            "Richmond District": 21,
            "Union Square": 9,
            "Fisherman's Wharf": 10,
            "Marina District": 15,
            "Haight-Ashbury": 19,
            "Mission District": 17,
            "Pacific Heights": 13,
            "Golden Gate Park": 23
        },
        "Union Square": {
            "The Castro": 17,
            "Alamo Square": 15,
            "Richmond District": 20,
            "Financial District": 9,
            "Fisherman's Wharf": 15,
            "Marina District": 18,
            "Haight-Ashbury": 18,
            "Mission District": 14,
            "Pacific Heights": 15,
            "Golden Gate Park": 22
        },
        "Fisherman's Wharf": {
            "The Castro": 27,
            "Alamo Square": 21,
            "Richmond District": 18,
            "Financial District": 11,
            "Union Square": 13,
            "Marina District": 9,
            "Haight-Ashbury": 22,
            "Mission District": 22,
            "Pacific Heights": 12,
            "Golden Gate Park": 25
        },
        "Marina District": {
            "The Castro": 22,
            "Alamo Square": 15,
            "Richmond District": 11,
            "Financial District": 17,
            "Union Square": 16,
            "Fisherman's Wharf": 10,
            "Haight-Ashbury": 16,
            "Mission District": 20,
            "Pacific Heights": 7,
            "Golden Gate Park": 18
        },
        "Haight-Ashbury": {
            "The Castro": 6,
            "Alamo Square": 5,
            "Richmond District": 10,
            "Financial District": 21,
            "Union Square": 19,
            "Fisherman's Wharf": 23,
            "Marina District": 17,
            "Mission District": 11,
            "Pacific Heights": 12,
            "Golden Gate Park": 7
        },
        "Mission District": {
            "The Castro": 7,
            "Alamo Square": 11,
            "Richmond District": 20,
            "Financial District": 15,
            "Union Square": 15,
            "Fisherman's Wharf": 22,
            "Marina District": 19,
            "Haight-Ashbury": 12,
            "Pacific Heights": 16,
            "Golden Gate Park": 17
        },
        "Pacific Heights": {
            "The Castro": 16,
            "Alamo Square": 10,
            "Richmond District": 12,
            "Financial District": 13,
            "Union Square": 12,
            "Fisherman's Wharf": 13,
            "Marina District": 6,
            "Haight-Ashbury": 11,
            "Mission District": 15,
            "Golden Gate Park": 15
        },
        "Golden Gate Park": {
            "The Castro": 13,
            "Alamo Square": 9,
            "Richmond District": 7,
            "Financial District": 26,
            "Union Square": 22,
            "Fisherman's Wharf": 24,
            "Marina District": 16,
            "Haight-Ashbury": 7,
            "Mission District": 17,
            "Pacific Heights": 16
        }
    }
    
    # Define meeting constraints.
    # All times are in minutes from midnight.
    # 9:00 AM is 540 minutes.
    meeting_data = {
        "Anthony": {
            "location": "Haight-Ashbury",
            "available_start": 435,  # 7:15
            "available_end": 630,    # 10:30
            "duration": 30
        },
        "Helen": {
            "location": "Pacific Heights",
            "available_start": 480,  # 8:00
            "available_end": 720,    # 12:00
            "duration": 75
        },
        "Joseph": {
            "location": "Financial District",
            "available_start": 675,  # 11:15
            "available_end": 810,    # 13:30
            "duration": 15
        },
        "Karen": {
            "location": "Marina District",
            "available_start": 690,  # 11:30
            "available_end": 1110,   # 18:30
            "duration": 15
        },
        "Joshua": {
            "location": "Richmond District",
            "available_start": 420,  # 7:00
            "available_end": 1200,   # 20:00
            "duration": 15
        },
        "Brian": {
            "location": "Fisherman's Wharf",
            "available_start": 825,  # 13:45
            "available_end": 1245,   # 20:45
            "duration": 105
        },
        "William": {
            "location": "Alamo Square",
            "available_start": 915,  # 15:15
            "available_end": 1035,   # 17:15
            "duration": 60
        },
        "David": {
            "location": "Union Square",
            "available_start": 1005, # 16:45
            "available_end": 1155,   # 19:15
            "duration": 45
        },
        "Matthew": {
            "location": "Mission District",
            "available_start": 1035, # 17:15
            "available_end": 1155,   # 19:15
            "duration": 120
        },
        "Jeffrey": {
            "location": "Golden Gate Park",
            "available_start": 1140, # 19:00
            "available_end": 1290,   # 21:30
            "duration": 60
        }
    }
    
    # Start at The Castro at 9:00 AM.
    start_location = "The Castro"
    start_time = 540  # 9:00 AM
    
    # Build the early (common) part of the itinerary.
    common_order = [
        {"person": "Anthony", **meeting_data["Anthony"]},
        {"person": "Helen", **meeting_data["Helen"]},
        {"person": "Joseph", **meeting_data["Joseph"]},
        {"person": "Karen", **meeting_data["Karen"]},
        {"person": "Joshua", **meeting_data["Joshua"]},
        {"person": "Brian", **meeting_data["Brian"]}
    ]
    
    # Two alternatives for the late afternoon:
    # Branch A: Meet William, then David, then Jeffrey.
    branch_A = common_order + [
        {"person": "William", **meeting_data["William"]},
        {"person": "David", **meeting_data["David"]},
        {"person": "Jeffrey", **meeting_data["Jeffrey"]}
    ]
    # Branch B: Meet William, then Matthew, then Jeffrey.
    branch_B = common_order + [
        {"person": "William", **meeting_data["William"]},
        {"person": "Matthew", **meeting_data["Matthew"]},
        {"person": "Jeffrey", **meeting_data["Jeffrey"]}
    ]
    
    schedule_A = compute_schedule(branch_A, start_location, start_time, travel_times)
    schedule_B = compute_schedule(branch_B, start_location, start_time, travel_times)
    
    # Choose the schedule that meets the most friends.
    # Both branches yield 9 meetings if feasible.
    # Tie-breaker: choose the one with the earlier finish time.
    finish_time_A = schedule_A[1] if schedule_A is not None else float('inf')
    finish_time_B = schedule_B[1] if schedule_B is not None else float('inf')
    
    if schedule_A is None and schedule_B is None:
        optimal_schedule = {"itinerary": []}
    elif schedule_A is not None and (schedule_B is None or finish_time_A <= finish_time_B):
        optimal_schedule = {"itinerary": schedule_A[0]}
    else:
        optimal_schedule = {"itinerary": schedule_B[0]}
    
    print(json.dumps(optimal_schedule, indent=2))

if __name__ == "__main__":
    main()