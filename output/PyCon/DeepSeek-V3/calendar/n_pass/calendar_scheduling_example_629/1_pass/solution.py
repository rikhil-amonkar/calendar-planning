from constraint import Problem

def main():
    problem = Problem()
    
    # Define days and time slots in minutes from 9:00 (540 minutes)
    days = ['Monday', 'Tuesday']
    start_min = 9 * 60  # 9:00 in minutes
    end_min = 17 * 60   # 17:00 in minutes
    meeting_duration = 30  # minutes
    
    # Convert blocked times to minutes from start of day
    margaret_blocked = {
        'Monday': [(10*60+30, 11*60), (11*60+30, 12*60), (13*60, 13*60+30), (15*60, 17*60)],
        'Tuesday': [(12*60, 12*60+30)]
    }
    
    alexis_blocked = {
        'Monday': [(9*60+30, 11*60+30), (12*60+30, 13*60), (14*60, 17*60)],
        'Tuesday': [(9*60, 9*60+30), (10*60, 10*60+30), (14*60, 16*60+30)]
    }
    
    # Add variables: day and start time (in minutes from 9:00)
    problem.addVariable('day', days)
    problem.addVariable('start_time', range(start_min, end_min - meeting_duration + 1))
    
    # Define constraint function
    def time_constraint(day, start_time):
        end_time = start_time + meeting_duration
        
        # Margaret's constraints
        margaret_no_monday = (day != 'Monday')  # Margaret doesn't want Monday
        margaret_no_tuesday_before_1430 = not (day == 'Tuesday' and start_time < 14*60+30)
        
        if not (margaret_no_monday and margaret_no_tuesday_before_1430):
            return False
        
        # Check Margaret's blocked times
        for block_start, block_end in margaret_blocked[day]:
            if not (end_time <= block_start or start_time >= block_end):
                return False
        
        # Check Alexis's blocked times
        for block_start, block_end in alexis_blocked[day]:
            if not (end_time <= block_start or start_time >= block_end):
                return False
        
        return True
    
    problem.addConstraint(time_constraint, ['day', 'start_time'])
    
    # Find solution
    solutions = problem.getSolutions()
    
    if solutions:
        solution = solutions[0]
        day = solution['day']
        start_minutes = solution['start_time']
        end_minutes = start_minutes + meeting_duration
        
        # Convert back to HH:MM format
        start_hour = start_minutes // 60
        start_minute = start_minutes % 60
        end_hour = end_minutes // 60
        end_minute = end_minutes % 60
        
        print(f"{day}: {start_hour:02d}:{start_minute:02d}-{end_hour:02d}:{end_minute:02d}")
    else:
        print("No suitable time found")

if __name__ == "__main__":
    main()