YOUR_CODE
from z3 import *

# Define the variables
day = 'Monday'
start_time = Int('start_time')
end_time = Int('end_time')
meeting_duration = 30  # in minutes

# Define the constraints for each participant
katherine_busy = [Bool('katherine_busy_%d' % i) for i in range(8)]
rebecca_busy = [Bool('rebecca_busy_%d' % i) for i in range(8)]
julie_busy = [Bool('julie_busy_%d' % i) for i in range(8)]
angela_busy = [Bool('angela_busy_%d' % i) for i in range(8)]
nicholas_busy = [Bool('nicholas_busy_%d' % i) for i in range(8)]
carl_busy = [Bool('carl_busy_%d' % i) for i in range(8)]

# Define the constraints
katherine_constraints = [
    katherine_busy[12] == True,
    katherine_busy[13] == True,
    And(katherine_busy[9] == False, katherine_busy[10] == False, katherine_busy[11] == False)
]
rebecca_constraints = [rebecca_busy[i] == False for i in range(8)]
julie_constraints = [
    julie_busy[9] == True,
    julie_busy[10] == True,
    julie_busy[13] == True,
    julie_busy[14] == True,
    julie_busy[15] == True,
    And(julie_busy[11] == False, julie_busy[12] == False, julie_busy[13] == False),
    And(julie_busy[16] == False, julie_busy[17] == False)
]
angela_constraints = [
    angela_busy[9] == True,
    angela_busy[10] == True,
    angela_busy[11] == True,
    angela_busy[14] == True,
    angela_busy[15] == True,
    angela_busy[16] == True,
    And(angela_busy[0] == False, angela_busy[1] == False, angela_busy[2] == False, angela_busy[3] == False, angela_busy[4] == False, angela_busy[5] == False, angela_busy[6] == False, angela_busy[7] == False),
    angela_busy[17] == True
]
nicholas_constraints = [
    nicholas_busy[10] == True,
    nicholas_busy[11] == True,
    nicholas_busy[14] == True,
    nicholas_busy[15] == True,
    nicholas_busy[16] == True,
    And(nicholas_busy[9] == False, nicholas_busy[10] == False, nicholas_busy[11] == False),
    nicholas_busy[17] == True
]
carl_constraints = [
    carl_busy[9] == True,
    carl_busy[10] == True,
    carl_busy[11] == True,
    carl_busy[14] == True,
    carl_busy[15] == True,
    carl_busy[16] == True,
    And(carl_busy[0] == False, carl_busy[1] == False, carl_busy[2] == False, carl_busy[3] == False, carl_busy[4] == False, carl_busy[5] == False, carl_busy[6] == False, carl_busy[7] == False),
    carl_busy[17] == True
]
angela_prefer = And(angela_busy[12] == False, angela_busy[13] == False, angela_busy[14] == False, angela_busy[15] == False)

# Define the solver
s = Solver()

# Add the constraints to the solver
s.add(katherine_constraints + rebecca_constraints + julie_constraints + angela_constraints + nicholas_constraints + carl_constraints)
s.add(angela_prefer)
s.add(And(start_time >= 9 * 60, start_time + meeting_duration <= 17 * 60, end_time >= start_time, end_time <= 17 * 60, start_time % 60 == 0, end_time % 60 == 0))

# Solve the problem
if s.check() == sat:
    model = s.model()
    start_time_val = model[start_time].as_long()
    end_time_val = model[end_time].as_long()
    print('SOLUTION:')
    print(f'Day: {day}')
    print(f'Start Time: {start_time_val // 60:02d}:{start_time_val % 60:02d}')
    print(f'End Time: {end_time_val // 60:02d}:{end_time_val % 60:02d}')
else:
    print('No solution found')