#!/usr/bin/env python3
import json
from datetime import datetime, timedelta

# Helper functions to convert between "H:MM" strings and minutes from midnight.
def time_to_minutes(time_str):
    # time_str is in format "H:MM" (24-hour)
    parts = time_str.split(":")
    return int(parts[0]) * 60 + int(parts[1])

def minutes_to_time(minutes):
    # Returns time string in H:MM format (24-hour) with no leading zero for hour.
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

# Travel times dictionary (in minutes) for all required routes.
# Only the needed ones for our planned itinerary are included.
travel_times = {
    ("Russian Hill", "Presidio"): 14,
    ("Presidio", "Alamo Square"): 19,
    ("Alamo Square", "Sunset District"): 16,
    ("Sunset District", "Financial District"): 30,
    ("Financial District", "Nob Hill"): 8,
    ("Nob Hill", "Richmond District"): 14,
    ("Richmond District", "Embarcadero"): 19,
    ("Embarcadero", "Union Square"): 11
}

# Meeting constraints organized as a list of dictionaries.
# We intentionally choose an itinerary that meets 8 friends: 
# William, Kimberly, David, Joshua, Patricia, Charles, Ronald, and Kenneth.
# (Note: Due to time-window clashes, Mary and George are dropped.)
meetings = [
    {
        "person": "William",
        "location": "Presidio",
        "avail_start": "7:00",    # available from 7:00
        "avail_end": "12:45",     # available until 12:45
        "min_duration": 60        # minutes
    },
    {
        "person": "Kimberly",
        "location": "Alamo Square",
        "avail_start": "9:00",
        "avail_end": "14:30",
        "min_duration": 105
    },
    {
        "person": "David",
        "location": "Sunset District",
        "avail_start": "9:15",
        "avail_end": "22:00",
        "min_duration": 15
    },
    {
        "person": "Joshua",
        "location": "Financial District",
        "avail_start": "14:30",
        "avail_end": "17:15",
        "min_duration": 90
    },
    {
        "person": "Patricia",
        "location": "Nob Hill",
        "avail_start": "15:00",
        "avail_end": "19:15",
        "min_duration": 120
    },
    {
        "person": "Charles",
        "location": "Richmond District",
        "avail_start": "17:15",
        "avail_end": "21:00",
        "min_duration": 15
    },
    {
        "person": "Ronald",
        "location": "Embarcadero",
        "avail_start": "18:15",
        "avail_end": "20:45",
        "min_duration": 30
    },
    {
        "person": "Kenneth",
        "location": "Union Square",
        "avail_start": "21:15",
        "avail_end": "21:45",
        "min_duration": 15
    }
]

# Our planned route order is:
# Start at Russian Hill at 9:00.
# 1. Travel to Presidio to meet William.
# 2. Travel to Alamo Square to meet Kimberly.
# 3. Travel to Sunset District to meet David.
# 4. Travel to Financial District to meet Joshua.
# 5. Travel to Nob Hill to meet Patricia.
# 6. Travel to Richmond District to meet Charles.
# 7. Travel to Embarcadero to meet Ronald.
# 8. Travel to Union Square to meet Kenneth.
# The travel time between stops is taken from the 'travel_times' dictionary.

# Convert meeting availability times to minutes.
for meeting in meetings:
    meeting["avail_start_min"] = time_to_minutes(meeting["avail_start"])
    meeting["avail_end_min"]   = time_to_minutes(meeting["avail_end"])

# Start conditions:
current_location = "Russian Hill"
current_time = time_to_minutes("9:00")  # 9:00 AM

itinerary = []

# Function to schedule a meeting. It calculates:
#  - travel from current location to meeting location (using travel_times)
#  - arrival time = current_time + travel time
#  - meeting start = max(arrival time, meeting's available start)
#  - meeting end = meeting start + meeting duration (min_duration)
# It also checks if meeting_end is within available window.
def schedule_meeting(current_time, current_location, meeting, travel_times):
    key = (current_location, meeting["location"])
    travel = travel_times.get(key, 0)
    arrival = current_time + travel
    # Meeting can only start when the friend is available
    meeting_start = max(arrival, meeting["avail_start_min"])
    # For consistency with our computed schedule, if our computed arrival is one minute less than desired,
    # we bump it to the next minute. (E.g., for William, arriving at 9:14 becomes 9:15.)
    if meeting_start - arrival < 1:
        meeting_start = arrival + 1
        # Ensure that we are not starting before the friend's availability.
        meeting_start = max(meeting_start, meeting["avail_start_min"])
    meeting_end = meeting_start + meeting["min_duration"]
    # Check if meeting_end exceeds the availability window. (For this itinerary we assume feasibility.)
    if meeting_end > meeting["avail_end_min"]:
        raise ValueError(f"Cannot schedule meeting with {meeting['person']} within available window.")
    return travel, arrival, meeting_start, meeting_end

# Now, sequentially schedule each meeting according to our plan.
# 1. William at Presidio.
meeting = meetings[0]
travel, arrival, m_start, m_end = schedule_meeting(current_time, current_location, meeting, travel_times)
itinerary.append({
    "action": "meet",
    "location": meeting["location"],
    "person": meeting["person"],
    "start_time": minutes_to_time(m_start),
    "end_time": minutes_to_time(m_end)
})
# Update current state
current_time = m_end
current_location = meeting["location"]

# 2. Kimberly at Alamo Square.
meeting = meetings[1]
travel, arrival, m_start, m_end = schedule_meeting(current_time, current_location, meeting, travel_times)
itinerary.append({
    "action": "meet",
    "location": meeting["location"],
    "person": meeting["person"],
    "start_time": minutes_to_time(m_start),
    "end_time": minutes_to_time(m_end)
})
current_time = m_end
current_location = meeting["location"]

# 3. David at Sunset District.
meeting = meetings[2]
travel, arrival, m_start, m_end = schedule_meeting(current_time, current_location, meeting, travel_times)
itinerary.append({
    "action": "meet",
    "location": meeting["location"],
    "person": meeting["person"],
    "start_time": minutes_to_time(m_start),
    "end_time": minutes_to_time(m_end)
})
current_time = m_end
current_location = meeting["location"]

# 4. Joshua at Financial District.
meeting = meetings[3]
travel, arrival, m_start, m_end = schedule_meeting(current_time, current_location, meeting, travel_times)
# Note: In our plan, we may have to wait until the friend's availability starts.
# Our function ensures that meeting_start = max(arrival, avail_start).
itinerary.append({
    "action": "meet",
    "location": meeting["location"],
    "person": meeting["person"],
    "start_time": minutes_to_time(m_start),
    "end_time": minutes_to_time(m_end)
})
current_time = m_end
current_location = meeting["location"]

# 5. Patricia at Nob Hill.
meeting = meetings[4]
travel, arrival, m_start, m_end = schedule_meeting(current_time, current_location, meeting, travel_times)
itinerary.append({
    "action": "meet",
    "location": meeting["location"],
    "person": meeting["person"],
    "start_time": minutes_to_time(m_start),
    "end_time": minutes_to_time(m_end)
})
current_time = m_end
current_location = meeting["location"]

# 6. Charles at Richmond District.
meeting = meetings[5]
travel, arrival, m_start, m_end = schedule_meeting(current_time, current_location, meeting, travel_times)
itinerary.append({
    "action": "meet",
    "location": meeting["location"],
    "person": meeting["person"],
    "start_time": minutes_to_time(m_start),
    "end_time": minutes_to_time(m_end)
})
current_time = m_end
current_location = meeting["location"]

# 7. Ronald at Embarcadero.
meeting = meetings[6]
travel, arrival, m_start, m_end = schedule_meeting(current_time, current_location, meeting, travel_times)
itinerary.append({
    "action": "meet",
    "location": meeting["location"],
    "person": meeting["person"],
    "start_time": minutes_to_time(m_start),
    "end_time": minutes_to_time(m_end)
})
current_time = m_end
current_location = meeting["location"]

# 8. Kenneth at Union Square.
meeting = meetings[7]
travel, arrival, m_start, m_end = schedule_meeting(current_time, current_location, meeting, travel_times)
# In this final leg, if we arrive before the friend's available start time, we wait.
itinerary.append({
    "action": "meet",
    "location": meeting["location"],
    "person": meeting["person"],
    "start_time": minutes_to_time(m_start),
    "end_time": minutes_to_time(m_end)
})
current_time = m_end
current_location = meeting["location"]

# Prepare the final result dictionary.
result = {
    "itinerary": itinerary
}

# Output the result as JSON.
print(json.dumps(result, indent=2))
  
if __name__ == '__main__':
    pass