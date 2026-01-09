from constraint import Problem

def main():
    problem = Problem()
    
    # Define days and time slots (in minutes from 9:00)
    days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday']
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    meeting_duration = 60  # 60 minutes
    
    # Add variables: day and start time (in minutes from 0:00)
    problem.addVariable('day', days)
    problem.addVariable('start_time', range(work_start, work_end - meeting_duration + 1))
    
    # Bryan's constraints (avoid Tuesday)
    def bryan_day_constraint(day, start_time):
        if day == 'Tuesday':
            return False
            
        # Bryan's meetings (converted to minutes from 0:00)
        bryan_meetings = {
            'Thursday': [(9*60+30, 10*60), (12*60+30, 13*60)],
            'Friday': [(10*60+30, 11*60), (14*60, 14*60+30)]
        }
        
        if day in bryan_meetings:
            meeting_end = start_time + meeting_duration
            for meeting_start, meeting_end_existing in bryan_meetings[day]:
                if not (meeting_end <= meeting_start or start_time >= meeting_end_existing):
                    return False
        return True
    
    # Nicholas's constraints (avoid Monday, Thursday)
    def nicholas_day_constraint(day, start_time):
        if day in ['Monday', 'Thursday']:
            return False
            
        # Nicholas's meetings (converted to minutes from 0:00)
        nicholas_meetings = {
            'Monday': [(11*60+30, 12*60), (13*60, 15*60+30)],
            'Tuesday': [(9*60, 9*60+30), (11*60, 13*60+30), (14*60, 16*60+30)],
            'Wednesday': [(9*60, 9*60+30), (10*60, 11*60), (11*60+30, 13*60+30), 
                         (14*60, 14*60+30), (15*60, 16*60+30)],
            'Thursday': [(10*60+30, 11*60+30), (12*60, 12*60+30), (15*60, 15*60+30), 
                        (16*60+30, 17*60)],
            'Friday': [(9*60, 10*60+30), (11*60, 12*60), (12*60+30, 14*60+30), 
                      (15*60+30, 16*60), (16*60+30, 17*60)]
        }
        
        if day in nicholas_meetings:
            meeting_end = start_time + meeting_duration
            for meeting_start, meeting_end_existing in nicholas_meetings[day]:
                if not (meeting_end <= meeting_start or start_time >= meeting_end_existing):
                    return False
        return True
    
    # Add constraints
    problem.addConstraint(bryan_day_constraint, ['day', 'start_time'])
    problem.addConstraint(nicholas_day_constraint, ['day', 'start_time'])
    
    # Find solution
    solutions = problem.getSolutions()
    
    if solutions:
        solution = solutions[0]
        day = solution['day']
        start_minutes = solution['start_time']
        end_minutes = start_minutes + meeting_duration
        
        # Convert to HH:MM format
        start_hour = start_minutes // 60
        start_minute = start_minutes % 60
        end_hour = end_minutes // 60
        end_minute = end_minutes % 60
        
        print(f"{day}")
        print(f"{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}")
    else:
        print("No suitable time found")

if __name__ == "__main__":
    main()