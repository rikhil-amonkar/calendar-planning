# Define the time slots from 9:00 to 17:00 in 30-minute increments
time_slots = [(9, 0), (9, 30), (10, 0), (10, 30), (11, 0), (11, 30), (12, 0), (12, 30),
              (13, 0), (13, 30), (14, 0), (14, 30), (15, 0), (15, 30), (16, 0), (16, 30)]

# Initialize availability lists for each participant
emily_availability = [True] * len(time_slots)
melissa_availability = [True] * len(time_slots)
frank_availability = [True] * len(time_slots)

# Mark Emily's busy times
busy_times_emily = [(10, 0), (10, 30), (11, 30), (12, 0), (14, 0), (14, 30), (16, 0), (16, 30)]
for time in busy_times_emily:
    index = time_slots.index(time)
    emily_availability[index] = False

# Mark Melissa's busy times
busy_times_melissa = [(9, 30), (14, 30), (15, 0)]
for time in busy_times_melissa:
    index = time_slots.index(time)
    melissa_availability[index] = False

# Mark Frank's busy times and constraint
busy_times_frank = [(10, 0), (10, 30), (11, 0), (11, 30), (12, 30), (13, 0), (13, 30), (14, 0), (14, 30),
                    (15, 0), (15, 30), (16, 0), (16, 30)]
for time in busy_times_frank:
    index = time_slots.index(time)
    frank_availability[index] = False

# Iterate over time slots to find a 30-minute window where all are available
for i in range(len(time_slots) - 1):
    if emily_availability[i] and melissa_availability[i] and frank_availability[i]:
        start_time = time_slots[i]
        end_time = time_slots[i + 1]
        # Format the time as HH:MM
        start_time_str = f"{start_time[0]:02}:{start_time[1]:02}"
        end_time_str = f"{end_time[0]:02}:{end_time[1]:02}"
        print(f"Meeting time: {start_time_str}:{end_time_str} on Monday")
        break