def find_best_availability(person1_busy_times, person2_busy_times, start_time, end_time):
  """
  Finds the best available time slot for a meeting between two people.

  Args:
    person1_busy_times: A list of tuples representing busy times for person 1, 
                       in the format (start_time, end_time).
    person2_busy_times: A list of tuples representing busy times for person 2, 
                       in the format (start_time, end_time).
    start_time: The start time of the workday.
    end_time: The end time of the workday.

  Returns:
    A tuple representing the best available time slot, 
    in the format (start_time, end_time), or None if no suitable time slot is found.
  """

  available_slots = []
  current_time = start_time

  while current_time < end_time:
    is_person1_free = True
    is_person2_free = True

    for busy_time in person1_busy_times:
      if current_time >= busy_time[0] and current_time < busy_time[1]:
        is_person1_free = False
        break

    for busy_time in person2_busy_times:
      if current_time >= busy_time[0] and current_time < busy_time[1]:
        is_person2_free = False
        break

    if is_person1_free and is_person2_free:
      available_slots.append((current_time, current_time + 0.5))  # Add 30 minutes

    current_time += 0.5  # Move to the next 30-minute interval

  if available_slots:
    # Return the earliest available slot
    return min(available_slots)
  else:
    return None

# Example usage:
harolds_busy_times = []  # Harold is free all day
patricks_busy_times = [(9, 9.5), (10.5, 12), (12.5, 13.5), (14, 14.5), (15, 16.5)]
start_time = 9
end_time = 17

best_time = find_best_availability(harolds_busy_times, patricks_busy_times, start_time, end_time)

if best_time:
  print(f"Here is a proposed meeting time: {best_time[0]} - {best_time[1]}")
else:
  print("No suitable time slot found.")
  