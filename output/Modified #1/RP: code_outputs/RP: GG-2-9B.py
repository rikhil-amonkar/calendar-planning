def find_meeting_time(harold_availability, patrick_availability):
  """
  Finds the earliest available half-hour slot for a meeting 
  between Harold and Patrick.

  Args:
    harold_availability: A dictionary representing Harold's availability 
                        (e.g., {"Monday": [9, 17]}).
    patrick_availability: A dictionary representing Patrick's availability 
                         (e.g., {"Monday": [9, 9:30, 10:30, 12, 12:30, 14, 15]}).

  Returns:
    A string representing the earliest available meeting time, 
    or None if no suitable time is found.
  """

  monday_start = 9
  monday_end = 17

  # Extract Monday's availability
  harold_monday = harold_availability.get("Monday", [monday_start, monday_end])
  patrick_monday = patrick_availability.get("Monday", [])

  # Find overlapping free slots
  available_slots = []
  for i in range(monday_start, monday_end, 30):  # Check every 30 minutes
    if i not in patrick_monday and i + 30 <= monday_end:
      available_slots.append((i, i + 30))

  # Return the earliest available slot
  if available_slots:
    return f"{available_slots[0][0]:02d}:{available_slots[0][0] // 60:02d}-{available_slots[0][1]:02d}:{available_slots[0][1] // 60:02d}"
  else:
    return None

# Example usage:
harold_availability = {"Monday": [9, 17]}

# ******* ERROR CAUSED, HAD TO COMMENT CODE BELOW *******: 
# 
# patrick_availability = {"Monday": [9, 9:30, 10:30, 12, 12:30, 14, 15]}
# 
# meeting_time = find_meeting_time(harold_availability, patrick_availability)
#
# if meeting_time:
#   print(f"The earliest available meeting time is: {meeting_time}")
# else:
#   print("No suitable meeting time found.")
  