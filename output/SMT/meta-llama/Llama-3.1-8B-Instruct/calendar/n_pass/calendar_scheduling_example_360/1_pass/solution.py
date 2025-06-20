from z3 import *

def find_meeting_time(day, start_time, end_time, participants):
    """
    Find a time that works for everyone's schedule and constraints.
    
    Args:
    day (str): The day to meet.
    start_time (str): The start time in 24-hour format.
    end_time (str): The end time in 24-hour format.
    participants (dict): A dictionary of participants with their schedules.
    
    Returns:
    str: A string representing the solution in the required format.
    """
    
    # Create a Z3 solver
    s = Solver()
    
    # Define the variables
    time_slots = []
    for i in range(9, 18):
        for j in range(0, 60, 30):
            time_slots.append((i, j))
    
    # Define the constraints
    for participant, schedule in participants.items():
        for time_slot in time_slots:
            is_free = True
            for start, end in schedule:
                if start <= time_slot[0] < end or start < time_slot[1] <= end:
                    is_free = False
                    break
            s.assert_or(Not(is_free))
    
    # Add the meeting duration constraint
    for time_slot in time_slots:
        if time_slot[0] + 0.5 <= 17 and time_slot[1] + 30 <= 60:
            s.assert_or(Not(time_slot[0] + 0.5 <= 17 and time_slot[1] + 30 <= 60))
    
    # Solve the constraints
    if s.check() == sat:
        # Get the model
        m = s.model()
        
        # Get the time slot that satisfies all constraints
        for time_slot in time_slots:
            if m.evaluate(And(time_slot[0] == time_slot[0], time_slot[1] == time_slot[1])).as_bool():
                return f"SOLUTION:\nDay: {day}\nStart Time: {time_slot[0]:02d}:{time_slot[1]:02d}\nEnd Time: {time_slot[0] + 0.5:02d}:{time_slot[1] + 30:02d}"
    
    # If no solution is found, return an error message
    return "No solution found"

# Define the participants and their schedules
participants = {
    "Emily": [(10, 30), (16, 30)],
    "Mason": [],
    "Maria": [(10, 30), (14, 30)],
    "Carl": [(9, 30), (10, 30), (10, 30), (13, 30), (14, 30), (16, 30)],
    "David": [(9, 30), (11, 0), (12, 30), (14, 0), (16, 0)],
    "Frank": [(9, 30), (11, 0), (12, 30), (14, 30), (17, 0)]
}

# Find a time that works for everyone's schedule and constraints
solution = find_meeting_time("Monday", 9, 17, participants)

# Print the solution
print(solution)