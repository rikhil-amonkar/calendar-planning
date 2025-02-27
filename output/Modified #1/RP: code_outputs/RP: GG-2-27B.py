def find_meeting_time(harold_availability, patrick_availability):
  """
  Finds the earliest available 30-minute slot for a meeting between Harold and Patrick.

  Args:
    harold_availability: A list of tuples representing Harold's available time slots.
    patrick_availability: A list of tuples representing Patrick's available time slots.

  Returns:
    A tuple representing the start and end time of the meeting, or None if no suitable slot is found.
  """

  # Combine both availabilities into a single list
  all_availability = harold_availability + patrick_availability

  # Sort the combined list by start time
  all_availability.sort(key=lambda x: x[0])

  # Iterate through the sorted list to find a matching 30-minute slot
  for start, end in all_availability:
    if end - start == 30:  # Check for 30-minute duration
      meeting_start = start
      meeting_end = end
      return meeting_start, meeting_end

  # No suitable slot found
  return None

# Define Harold's availability (he's free all day)
harold_availability = [(900, 1700)]  # Times in 24-hour format

# Define Patrick's availability
patrick_availability = [
    (930, 1030),
    (1200, 1230),
    (1330, 1400),
    (1430, 1500),
    (1630, 1700)
]

# Find the best meeting time
meeting_time = find_meeting_time(harold_availability, patrick_availability)

if meeting_time:
  print(f"Meeting scheduled from {meeting_time[0]:04} to {meeting_time[1]:04}")
else:
  print("No suitable meeting time found.")
  