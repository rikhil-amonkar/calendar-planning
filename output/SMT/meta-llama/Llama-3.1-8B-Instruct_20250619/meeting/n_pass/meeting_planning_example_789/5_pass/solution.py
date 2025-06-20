from z3 import *

# Define the variables
time = [Int(f't_{i}') for i in range(13)]
meet = [Bool(f'm_{i}') for i in range(8)]
friend = [Bool(f'f_{i}') for i in range(8)]

# Define the constraints
s = Solver()

# Time constraints
s.add(And([time[0] == 0]))  # Start at 9:00AM
s.add(And([time[i] >= time[i-1] + 15 for i in range(1, 13)]))  # Each meeting takes at least 15 minutes

# Meeting constraints
s.add(And([meet[i] == (time[i] >= 105) for i in range(8)]))  # Meet each friend for at least 105 minutes

# Friend availability
s.add(And([friend[i] == meet[i] for i in range(8)]))  # Can only meet friends that are available

# Betty's availability
s.add(And([meet[0] == (time[1] >= 7) & (time[1] <= 4*60+45)]))  # Meet Betty from 7:00AM to 4:45PM

# Melissa's availability
s.add(And([meet[1] == (time[2] >= 9*60+30) & (time[2] <= 5*60+15)]))  # Meet Melissa from 9:30AM to 5:15PM

# Joshua's availability
s.add(And([meet[2] == (time[3] >= 12*60+15) & (time[3] <= 19*60)]))  # Meet Joshua from 12:15PM to 7:00PM

# Jeffrey's availability
s.add(And([meet[3] == (time[4] >= 12*60+15) & (time[4] <= 18*60)]))  # Meet Jeffrey from 12:15PM to 6:00PM

# James's availability
s.add(And([meet[4] == (time[5] >= 7*60+30) & (time[5] <= 20*60)]))  # Meet James from 7:30AM to 8:00PM

# Anthony's availability
s.add(And([meet[5] == (time[6] >= 11*60+45) & (time[6] <= 13*60+30)]))  # Meet Anthony from 11:45AM to 1:30PM

# Timothy's availability
s.add(And([meet[6] == (time[7] >= 12*60+30) & (time[7] <= 14*60+45)]))  # Meet Timothy from 12:30PM to 2:45PM

# Emily's availability
s.add(And([meet[7] == (time[8] >= 19*60) & (time[8] <= 21*60)]))  # Meet Emily from 7:30PM to 9:30PM

# Meet exactly 6 people
s.add(Sum([If(meet[i], 1, 0) for i in range(8)]) == 6)

# Solve the problem
if s.check() == sat:
    m = s.model()
    schedule = []
    for i in range(1, 13):
        if m[time[i]].as_long() >= 15:
            schedule.append((m[time[i-1]].as_long(), m[time[i]].as_long()))
    print('SOLUTION:')
    for i in range(len(schedule)):
        print(f'Meet at {schedule[i][0]/60}:{int(schedule[i][0]%60)}AM and {schedule[i][1]/60}:{int(schedule[i][1]%60)}AM')
else:
    print('No solution found')