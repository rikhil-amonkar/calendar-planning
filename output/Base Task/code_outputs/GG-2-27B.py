def find_meeting_time(harold_availability, patrick_availability):
  
  """
Finds a 30-minute meeting slot that works for both Harold and Patrick.

  Args:
    harold_availability: A list of tuples representing Harold's available time slots.
      Each tuple is in the format (start_time, end_time), where times are in 24-hour format.
    patrick_availability: A list of tuples representing Patrick's available time slots.
      Each tuple is in the format (start_time, end_time), where times are in 24-hour format.

  Returns:
    A tuple representing the start and end time of the meeting, or None if no suitable slot is found.
  """

  for harold_start, harold_end in harold_availability:
    for patrick_start, patrick_end in patrick_availability:
      # Check for overlap of at least 30 minutes
      if harold_start < patrick_end and patrick_start < harold_end:
        meeting_start = max(harold_start, patrick_start)
        meeting_end = min(harold_end, patrick_end)
        if meeting_end - meeting_start >= 0.5:  # 30 minutes in hours
          return (meeting_start, meeting_end)

  return None

# Define Harold's availability (open all day)
harold_availability = [(9.0, 17.0)]

# Define Patrick's availability
patrick_availability = [
    (9.30, 10.30),
    (12.0, 12.30),
    (13.30, 14.0),
    (14.30, 15.0),
    (16.30, 17.0)
]

meeting_time = find_meeting_time(harold_availability, patrick_availability)

if meeting_time:
  print(f"Meeting scheduled from {meeting_time[0]:.2f} to {meeting_time[1]:.2f}")
else:
  print("No suitable meeting time found.")
