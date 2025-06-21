from z3 import *

def schedule_meeting(day, start_time, end_time, participants, constraints, preferences):
    # Create a Z3 solver
    s = Solver()

    # Define the variables
    meeting_time = [Bool(f'meeting_time_{i}') for i in range(len(participants))]
    for i in range(len(participants)):
        s.add(meeting_time[i] == False)

    # Add constraints for each participant
    for participant in participants:
        if participant in constraints:
            for constraint in constraints[participant]:
                start, end = constraint
                for i in range(len(participants)):
                    s.add(Implies(meeting_time[i], start <= start_time + (i * 30) <= end))

    # Add constraints for the meeting duration
    for i in range(len(participants)):
        s.add(Implies(meeting_time[i], start_time + (i * 30) <= end_time))

    # Add constraints for the day
    s.add(start_time >= 9 * 60)
    s.add(end_time <= 17 * 60)

    # Add constraints for the preferences
    for participant in participants:
        if participant in preferences:
            for preference in preferences[participant]:
                start, end = preference
                for i in range(len(participants)):
                    s.add(Implies(meeting_time[i], start <= start_time + (i * 30) <= end))

    # Add constraints to ensure a meeting is scheduled
    s.add(Or(*meeting_time))

    # Check the solver
    if s.check() == sat:
        # Get the model
        m = s.model()

        # Get the meeting time
        meeting_time_value = []
        for i in range(len(participants)):
            meeting_time_value.append(m[meeting_time[i]].as_long())

        # Find the first meeting time that is True
        for i in range(len(participants)):
            if meeting_time_value[i] == 1:
                start_time_value = start_time + (i * 30)
                end_time_value = start_time_value + 30
                break

        # Print the solution
        print(f'SOLUTION:')
        print(f'Day: {day}')
        print(f'Start Time: {start_time_value // 60:02d}:{start_time_value % 60:02d}')
        print(f'End Time: {end_time_value // 60:02d}:{end_time_value % 60:02d}')
    else:
        # Add constraints to ensure Roger meets after 12:30
        for i in range(len(participants)):
            if participants[i] == 'Roger':
                s.add(Implies(meeting_time[i], start_time + (i * 30) >= 12 * 60 + 30))

        # Check the solver again
        if s.check() == sat:
            # Get the model
            m = s.model()

            # Get the meeting time
            meeting_time_value = []
            for i in range(len(participants)):
                meeting_time_value.append(m[meeting_time[i]].as_long())

            # Find the first meeting time that is True
            for i in range(len(participants)):
                if meeting_time_value[i] == 1:
                    start_time_value = start_time + (i * 30)
                    end_time_value = start_time_value + 30
                    break

            # Print the solution
            print(f'SOLUTION:')
            print(f'Day: {day}')
            print(f'Start Time: {start_time_value // 60:02d}:{start_time_value % 60:02d}')
            print(f'End Time: {end_time_value // 60:02d}:{end_time_value % 60:02d}')
        else:
            print('No solution found')

# Define the participants, constraints, and preferences
participants = ['Daniel', 'Kathleen', 'Carolyn', 'Roger', 'Cheryl', 'Virginia', 'Angela']
constraints = {
    'Kathleen': [(14 * 60 + 30, 15 * 60 + 30)],
    'Carolyn': [(12 * 60 + 0, 12 * 60 + 30), (13 * 60 + 0, 13 * 60 + 30)],
    'Cheryl': [(9 * 60 + 0, 9 * 60 + 30), (10 * 60 + 0, 11 * 60 + 30), (12 * 60 + 30, 13 * 60 + 30), (14 * 60 + 0, 17 * 60 + 0)],
    'Virginia': [(9 * 60 + 30, 11 * 60 + 30), (12 * 60 + 0, 12 * 60 + 30), (13 * 60 + 0, 13 * 60 + 30), (14 * 60 + 30, 15 * 60 + 30), (16 * 60 + 0, 17 * 60 + 0)],
    'Angela': [(9 * 60 + 30, 10 * 60 + 0), (10 * 60 + 30, 11 * 60 + 30), (12 * 60 + 0, 12 * 60 + 30), (13 * 60 + 0, 13 * 60 + 30), (14 * 60 + 0, 16 * 60 + 30)]
}
preferences = {
    'Roger': [(12 * 60 + 30, 17 * 60 + 0)]
}

# Schedule the meeting
schedule_meeting('Monday', 9 * 60, 17 * 60, participants, constraints, preferences)