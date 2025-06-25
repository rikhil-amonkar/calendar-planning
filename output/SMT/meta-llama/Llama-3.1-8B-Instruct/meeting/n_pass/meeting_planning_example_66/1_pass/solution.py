from z3 import *

# Define the time slots
time_slots = [9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]

# Define the variables
nob_hill = [Bool(f'Nob_Hill_{t}') for t in time_slots]
presidio = [Bool(f'Presidio_{t}') for t in time_slots]

# Define the constraints
s = Solver()
for t in time_slots:
    s.add(nob_hill[t]!= presidio[t])  # You can't be at both places at the same time

# You arrive at Nob Hill at 9:00AM
s.add(nob_hill[0])
s.add(nob_hill[9])  # You stay at Nob Hill until 9:00AM

# Robert will be at Presidio from 11:15AM to 5:45PM
robert_time_slots = [11, 12, 13, 14, 15, 16, 17, 18, 19, 20]
for t in robert_time_slots:
    s.add(presidio[t])  # You need to be at Presidio during Robert's time slots

# You'd like to meet Robert for a minimum of 120 minutes
min_meeting_time = 2  # Convert 120 minutes to hours
for t in range(11, 19):
    s.add(If(nob_hill[t] == True, presidio[t] == True, presidio[t] == False))  # If you're at Nob Hill, you need to be at Presidio

# Solve the constraints
s.check()
model = s.model()

# Print the schedule
print("Schedule:")
for t in time_slots:
    nob_hill_value = model[nob_hill[t]].as_bool()
    presidio_value = model[presidio[t]].as_bool()
    print(f"{t}:00 AM - Nob Hill: {nob_hill_value}, Presidio: {presidio_value}")

# Calculate the total travel time
travel_times = [
    (17, 18),  # Nob Hill to Presidio
    (18, 17)  # Presidio to Nob Hill
]
total_travel_time = 0
for i in range(len(time_slots) - 1):
    nob_hill_value = model[nob_hill[i]].as_bool()
    presidio_value = model[presidio[i]].as_bool()
    if nob_hill_value and presidio_value:
        total_travel_time += travel_times[0][0]
    elif not nob_hill_value and presidio_value:
        total_travel_time += travel_times[0][1]
print(f"\nTotal travel time: {total_travel_time} minutes")