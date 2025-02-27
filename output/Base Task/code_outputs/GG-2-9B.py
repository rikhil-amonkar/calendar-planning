def find_best_availability(harold_schedule, patrick_schedule):
  """
  Finds the best available time slot for a meeting between Harold and Patrick.

  Args:
    harold_schedule: A list of tuples representing Harold's busy times, 
                     e.g., [(9, 10), (12, 13)].
    patrick_schedule: A list of tuples representing Patrick's busy times, 
                     e.g., [(9, 9:30), (10:30, 12), (12:30, 13:30), (14, 14:30), (15, 16:30)].

  Returns:
    A tuple representing the best available time slot, 
    e.g., (13:30, 14).
  """

  # Convert time strings to datetime objects for easier comparison
  # (You'll need to install the datetime library if you haven't already)
  import datetime

  harold_schedule = [(datetime.datetime.strptime(t[0], '%H:%M'), datetime.datetime.strptime(t[1], '%H:%M')) for t in harold_schedule]
  patrick_schedule = [(datetime.datetime.strptime(t[0], '%H:%M'), datetime.datetime.strptime(t[1], '%H:%M')) for t in patrick_schedule]

  # Find all possible 30-minute slots within the workday
  available_slots = []
  for i in range(9, 17):
    start_time = datetime.datetime(2023, 10, 23, i, 0)  # Replace with actual date
    end_time = start_time + datetime.timedelta(minutes=30)
    available_slots.append((start_time, end_time))

  # Filter out slots that conflict with either Harold or Patrick's schedule
  free_slots = []
  for slot in available_slots:
    is_free_for_harold = True
    is_free_for_patrick = True
    for busy_slot in harold_schedule:
      if slot[0] <= busy_slot[1] and slot[1] >= busy_slot[0]:
        is_free_for_harold = False
        break
    for busy_slot in patrick_schedule:
      if slot[0] <= busy_slot[1] and slot[1] >= busy_slot[0]:
        is_free_for_patrick = False
        break
    if is_free_for_harold and is_free_for_patrick:
      free_slots.append(slot)

  # Return the first available slot (you could choose a different strategy here)
  if free_slots:
    return free_slots[0]
  else:
    return None

# Example usage:
harold_schedule = []  # Harold is free all day
patrick_schedule = [('9:00', '9:30'), ('10:30', '12:00'), ('12:30', '13:30'), ('14:00', '14:30'), ('15:00', '16:30')]

best_time = find_best_availability(harold_schedule, patrick_schedule)

if best_time:
  print(f"The best available time for the meeting is: {best_time[0].strftime('%H:%M')} - {best_time[1].strftime('%H:%M')}")
else:
  print("No suitable time slots found.")
  