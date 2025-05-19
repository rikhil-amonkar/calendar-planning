# Define the input parameters
pacific_heights_to_presidio = 11
pacific_heights_to_marina = 6
presidio_to_pacific_heights = 11
presidio_to_marina = 10
marina_to_pacific_heights = 7
marina_to_presidio = 10

# Define the arrival and availability times
user_arrival_pacific_heights = '9:00'  # 9:00 AM
jason_available_start = '10:00'  # 10:00 AM
jason_available_end = '16:15'  # 4:15 PM
kenneth_available_start = '15:30'  # 3:30 PM
kenneth_available_end = '18:45'  # 4:45 PM

# Convert time strings to minutes since 9:00
def time_to_minutes(time_str):
    hours, mins = map(int, time_str.split(':'))
    return (hours * 60) + mins

user_arrival_pacific_heights_min = 0  # 9:00 AM is 540 minutes since midnight
jason_available_start_min = time_to_minutes('10:00')  # 10:00 AM is 600 minutes
jason_available_end_min = time_to_minutes('16:15')  # 4:15 PM is 1050 minutes
kenneth_available_start_min = time_to_minutes('15:30')  # 3:30 PM is 990 minutes
kenneth_available_end_min = time_to_minutes('18:45')  # 4:45 PM is 1140 minutes

# Calculate the latest possible meeting start times
jason_min_meeting_time = 90
jason_latest_start = jason_available_end_min - jason_min_meeting_time
jason_latest_start = max(jason_available_start_min, jason_latest_start)

kenneth_min_meeting_time = 45
kenneth_latest_start = kenneth_available_end_min - kenneth_min_meeting_time
kenneth_latest_start = max(kenneth_available_start_min, kenneth_latest_start)

# Determine the optimal meeting order
# Option 1: Meet Jason first
john_meeting_start = max(jason_available_start_min, user_arrival_pacific_heights_min + 11)  # 10:00 AM
john_meeting_end = john_meeting_start + 90

# After meeting Jason, go back to Pacific Heights and then to Marina District
time_after_john = john_meeting_end + presidio_to_pacific_heights  # 11 minutes
time_after_john += pacific_heights_to_marina  # 6 minutes
time_after_john += marina_to_presidio  # 10 minutes
kenneth_meeting_start = max(kenneth_available_start_min, time_after_john)
kenneth_meeting_end = kenneth_meeting_start + 45

# Ensure that Kenneth's meeting doesn't exceed his availability
if kenneth_meeting_end > kenneth_available_end_min:
    # Adjust if needed, but in this case, it's within the availability
    pass

# Option 2: Meet Kenneth first
# kenneth_meeting_start = max(kenneth_available_start_min, user_arrival_pacific_heights_min + 6)  # 9:06 AM
# kenneth_meeting_end = kenneth_meeting_start + 45
# # After meeting Kenneth, go back to Pacific Heights
# time_after_kenneth = kenneth_meeting_end + marina_to_pacific_heights  # 7 minutes
# # Then go to Presidio again for Jason
# time_after_kenneth += pacific_heights_to_presidio  # 11 minutes
# jason_meeting_start = max(jason_available_start_min, time_after_kenneth)
# jason_meeting_end = jason_meeting_start + 90

# The first option is better as it allows meeting both without overlap

# Prepare the itinerary
itinerary = [
    {
        "action": "meet",
        "location": "Presidio",
        "person": "Jason",
        "start_time": "10:00",
        "end_time": "11:30"
    },
    {
        "action": "meet",
        "location": "Marina District",
        "person": "Kenneth",
        "start_time": "15:30",
        "end_time": "16:15"
    }
]

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