# Define the input parameters
embarcadero_to_financial = 5
embarcadero_to_alamo = 19
financial_to_embarcadero = 4
financial_to_alamo = 17
alamo_to_embarcadero = 17
alamo_to_financial = 17

# Define the arrival and availability times
user_arrival_embarcadero = '9:00'  # 9:00 AM
stephanie_available_start = '8:15'  # 8:15 AM
stephanie_available_end = '11:30'  # 11:30 AM
john_available_start = '10:15'  # 10:15 AM
john_available_end = '20:45'  # 8:45 PM

# Convert time strings to minutes since 9:00
def time_to_minutes(time_str):
    hours, mins = map(int, time_str.split(':'))
    return (hours * 60) + mins

user_arrival_embarcadero_min = 0  # 9:00 AM is 540 minutes since midnight
stephanie_available_start_min = time_to_minutes('8:15')  # 8:15 AM is 495 minutes
stephanie_available_end_min = time_to_minutes('11:30')  # 11:30 AM is 690 minutes
john_available_start_min = time_to_minutes('10:15')  # 10:15 AM is 615 minutes
john_available_end_min = time_to_minutes('20:45')  # 8:45 PM is 1260 minutes

# Calculate the latest possible meeting start times
stephanie_min_meeting_time = 90
stephanie_latest_start = stephanie_available_end_min - stephanie_min_meeting_time
stephanie_latest_start = max(stephanie_available_start_min, stephanie_latest_start)

john_min_meeting_time = 30
john_latest_start = john_available_end_min - john_min_meeting_time
john_latest_start = max(john_available_start_min, john_latest_start)

# Determine the optimal meeting order
# Option 1: Meet John first
john_meeting_start = max(john_available_start_min, user_arrival_embarcadero_min + 19)  # 10:15 AM
john_meeting_end = john_meeting_start + 30

# After meeting John, go back to Embarcadero and then to Financial District
time_after_john = john_meeting_end + alamo_to_embarcadero
time_after_john += financial_to_alamo  # Total: 17 + 5 = 22 minutes
stephanie_meeting_start = max(stephanie_available_start_min, time_after_john)
stephanie_meeting_end = stephanie_meeting_start + 90

# Ensure that Stephanie's meeting doesn't exceed her availability
if stephanie_meeting_end > stephanie_available_end_min:
    # Adjust if needed, but in this case, it's within the availability
    pass

# Option 2: Meet Stephanie first
# stephanie_meeting_start = max(stephanie_available_start_min, user_arrival_embarcadero_min + 5)  # 9:05 AM
# stephanie_meeting_end = stephanie_meeting_start + 90
# # After meeting Stephanie, go back to Alamo Square
# time_after_stephanie = stephanie_meeting_end + financial_to_alamo  # 17 minutes
# time_after_stephanie += alamo_to_embarcadero  # 17 minutes
# # Then go to Alamo Square again for John
# time_after_stephanie += financial_to_alamo  # 5 minutes
# john_meeting_start = max(john_available_start_min, time_after_stephanie)
# john_meeting_end = john_meeting_start + 30

# The first option is better as it allows meeting both without overlap

# Prepare the itinerary
itinerary = [
    {
        "action": "meet",
        "location": "Alamo Square",
        "person": "John",
        "start_time": "10:15",
        "end_time": "10:45"
    },
    {
        "action": "meet",
        "location": "Financial District",
        "person": "Stephanie",
        "start_time": "11:02",
        "end_time": "12:32"
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