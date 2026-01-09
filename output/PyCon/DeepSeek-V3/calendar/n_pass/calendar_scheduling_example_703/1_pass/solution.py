from constraint import Problem
import datetime

def main():
    problem = Problem()
    
    # Define days and time slots in minutes from 9:00 (540 minutes) to 17:00 (1020 minutes)
    days = ['Monday', 'Tuesday', 'Wednesday']
    start_min = 540  # 9:00 in minutes
    end_min = 1020   # 17:00 in minutes
    meeting_duration = 60  # 1 hour in minutes
    
    # Add variables: day and start time (in minutes from midnight)
    problem.addVariable('day', days)
    problem.addVariable('start_time', range(start_min, end_min - meeting_duration + 1))
    
    # Stephanie's meetings (in minutes from midnight)
    stephanie_meetings = {
        'Monday': [(570, 600), (630, 660), (690, 720), (840, 870)],
        'Tuesday': [(720, 780)],
        'Wednesday': [(540, 600), (780, 840)]
    }
    
    # Betty's meetings (in minutes from midnight)
    betty_meetings = {
        'Monday': [(540, 600), (660, 690), (870, 900), (930, 960)],
        'Tuesday': [(540, 570), (690, 720), (750, 870), (930, 960)],
        'Wednesday': [(600, 690), (720, 840), (870, 1020)]
    }
    
    def time_overlap(meeting1_start, meeting1_end, meeting2_start, meeting2_end):
        return not (meeting1_end <= meeting2_start or meeting1_start >= meeting2_end)
    
    def is_available(day, start_time):
        end_time = start_time + meeting_duration
        
        # Check Stephanie's availability
        for meeting_start, meeting_end in stephanie_meetings.get(day, []):
            if time_overlap(start_time, end_time, meeting_start, meeting_end):
                return False
        
        # Check Betty's availability
        for meeting_start, meeting_end in betty_meetings.get(day, []):
            if time_overlap(start_time, end_time, meeting_start, meeting_end):
                return False
        
        # Stephanie prefers to avoid more meetings on Monday
        if day == 'Monday':
            return False
        
        # Betty cannot meet on Tuesday after 12:30 (750 minutes)
        if day == 'Tuesday' and start_time >= 750:
            return False
        
        return True
    
    problem.addConstraint(is_available, ['day', 'start_time'])
    
    solutions = problem.getSolutions()
    
    if solutions:
        solution = solutions[0]
        day = solution['day']
        start_minutes = solution['start_time']
        end_minutes = start_minutes + meeting_duration
        
        # Convert minutes to HH:MM format
        start_time_str = f"{start_minutes // 60:02d}:{start_minutes % 60:02d}"
        end_time_str = f"{end_minutes // 60:02d}:{end_minutes % 60:02d}"
        
        print(f"{day}: {start_time_str}-{end_time_str}")
    else:
        print("No suitable meeting time found")

if __name__ == "__main__":
    main()