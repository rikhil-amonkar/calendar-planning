def find_earliest_available_time(busy_times, start_time, end_time):
  """
  Finds the earliest available 30-minute slot within a given time range,
  avoiding specified busy times.

  Args:
    busy_times: A list of tuples representing busy time slots in the format (start, end).
    start_time: The start time of the available time range (inclusive).
    end_time: The end time of the available time range (inclusive).

  Returns:
    A tuple representing the earliest available time slot (start, end), 
    or None if no suitable slot is found.
  """

  available_slots = []
  current_time = start_time

  while current_time < end_time:
    is_busy = False
    for busy_start, busy_end in busy_times:
      if current_time >= busy_start and current_time < busy_end:
        is_busy = True
        break

    if not is_busy:
      available_slots.append((current_time, current_time + 30))
      current_time += 30
    else:
      current_time += 1  # Move to the next minute

  if available_slots:
    return min(available_slots, key=lambda x: x[0])  
  else:
    return None

# Example usage:
harolds_availability = [(9, 17)]  # Harold is available all day
patricks_busy_times = [(9, 9.5), (10.5, 12), (12.5, 13.5), (14, 14.5), (15, 16.5)]

earliest_time = find_earliest_available_time(patricks_busy_times, 9, 17)

if earliest_time:
  print(f"The earliest available time is: {earliest_time}")
else:
  print("No suitable time slot found.") 
  