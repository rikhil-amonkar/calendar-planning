# Define the input parameters
sunset_district_to_chinatown = 30
sunset_district_to_russian_hill = 24
sunset_district_to_north_beach = 29
ch Chinatown_to_sunset_district = 29
ch Chinatown_to_russian_hill = 7
ch Chinatown_to_north_beach = 3
russian_hill_to_sunset_district = 23
russian_hill_to_chinatown = 9
russian_hill_to_north_beach = 5
north_beach_to_sunset_district = 27
north_beach_to_chinatown = 6
north_beach_to_russian_hill = 4

# Define the arrival and availability times
user_arrival_sunset_district = '9:00'  # 9:00 AM
anthony_available_start = '13:15'  # 1:15 PM
anthony_available_end = '14:30'  # 2:30 PM
rebecca_available_start = '19:30'  # 7:30 PM
rebecca_available_end = '21:15'  # 9:15 PM
melissa_available_start = '8:15'  # 8:15 AM
melissa_available_end = '13:30'  # 1:30 PM

# Convert time strings to minutes since 9:00
def time_to_minutes(time_str):
    hours, mins = map(int, time_str.split(':'))
    return (hours * 60) + mins

user_arrival_sunset_district_min = 0  # 9:00 AM is 540 minutes since midnight
anthony_available_start_min = time_to_minutes('13:15')  # 1:15 PM is 765 minutes
anthony_available_end_min = time_to_minutes('14:30')  # 2:30 PM is 870 minutes
rebecca_available_start_min = time_to_minutes('19:30')  # 7:30 PM is 1170 minutes
rebecca_available_end_min = time_to_minutes('21:15')  # 9:15 PM is 1320 minutes
melissa_available_start_min = time_to_minutes('8:15')  # 8:15 AM is 495 minutes
melissa_available_end_min = time_to_minutes('13:30')  # 1:30 PM is 810 minutes

# Calculate the latest possible meeting start times
anthony_min_meeting_time = 60
anthony_latest_start = anthony_available_end_min - anthony_min_meeting_time
anthony_latest_start = max(anthony_available_start_min, anthony_latest_start)

rebecca_min_meeting_time = 105
rebecca_latest_start = rebecca_available_end_min - rebecca_min_meeting_time
rebecca_latest_start = max(rebecca_available_start_min, rebecca_latest_start)

melissa_min_meeting_time = 105
melissa_latest_start = melissa_available_end_min - melissa_min_meeting_time
melissa_latest_start = max(melissa_available_start_min, melissa_latest_start)

# Determine the optimal meeting order
# Option 1: Meet Melissa first
melissa_meeting_start = max(melissa_available_start_min, user_arrival_sunset_district_min + sunset_district_to_north_beach)  # 8:29 AM
melissa_meeting_end = melissa_meeting_start + 105

# After meeting Melissa, go back to Sunset District
time_after_melissa = melissa_meeting_end + north_beach_to_sunset_district  # 27 minutes
time_after_melissa += north_beach_to_chinatown  # 6 minutes

# Now, check the next available time
next_available_time = max(time_after_melissa, melissa_meeting_end + 1)

# Option 2: Meet Anthony
anthony_meeting_start = max(anthony_available_start_min, next_available_time)
if anthony_meeting_start + anthony_min_meeting_time <= anthony_available_end_min:
    anthony_meeting_end = anthony_meeting_start + 60
    # After meeting Anthony, go back to Sunset District
    time_after_anthony = anthony_meeting_end + chinatown_to_sunset_district  # 29 minutes
    time_after_anthony += russian_hill_to_sunset_district  # 23 minutes
    user_arrival_sunset_district_min = time_after_anthony
    # Check next available time
    next_available_time = max(user_arrival_sunset_district_min, anthony_meeting_end + 1)
else:
    # Cannot meet Anthony
    anthony_meeting_start = None
    anthony_meeting_end = None

# Option 3: Meet Rebecca
if not anthony_meeting_start:
    rebecca_meeting_start = max(rebecca_available_start_min, next_available_time)
    if rebecca_meeting_start + rebecca_min_meeting_time <= rebecca_available_end_min:
        rebecca_meeting_end = rebecca_meeting_start + 105
        # After meeting Rebecca, go back to Sunset District
        time_after_rebecca = rebecca_meeting_end + russian_hill_to_sunset_district  # 23 minutes
        time_after_rebecca += russian_hill_to_north_beach  # 5 minutes
        time_after_rebecca += north_beach_to_sunset_district  # 27 minutes
        user_arrival_sunset_district_min = time_after_rebecca
        # Check next available time
        next_available_time = max(user_arrival_sunset_district_min, rebecca_meeting_end + 1)
    else:
        rebecca_meeting_start = None
        rebecca_meeting_end = None

# Prepare the itinerary
itinerary = []
if melissa_meeting_start:
    itinerary.append({
        "action": "meet",
        "location": "North Beach",
        "person": "Melissa",
        "start_time": "08:29",
        "end_time": "09:34"
    })
if anthony_meeting_start:
    itinerary.append({
        "action": "meet",
        "location": "Chinatown",
        "person": "Anthony",
        "start_time": "10:34",
        "end_time": "11:34"
    })
if rebecca_meeting_start:
    itinerary.append({
        "action": "meet",
        "location": "Russian Hill",
        "person": "Rebecca",
        "start_time": "13:34",
        "end_time": "14:39"
    })

# Convert minutes back to time strings for output
def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

# Convert the itinerary times
for item in itinerary:
    start = minutes_to_time(item["start_time"])
    end = minutes_to_time(item["end_time"])
    item["start_time"] = start
    item["end_time"] = end

# Output the result as JSON
print({
    "itinerary": itinerary
})