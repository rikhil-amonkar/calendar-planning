from constraint import Problem
import datetime

def main():
    problem = Problem()
    
    days = ['Monday', 'Tuesday', 'Wednesday']
    start_hours = list(range(9, 17))
    
    # Define variables: day and start hour
    problem.addVariable('day', days)
    problem.addVariable('start_hour', start_hours)
    problem.addVariable('start_minute', [0, 30])
    
    # Robert's constraints (avoid Monday if possible)
    def robert_available(day, start_hour, start_minute):
        start_time = datetime.time(start_hour, start_minute)
        end_time_minutes = start_hour * 60 + start_minute + 30
        end_hour = end_time_minutes // 60
        end_minute = end_time_minutes % 60
        end_time = datetime.time(end_hour, end_minute)
        
        # Robert's busy times
        robert_busy = {
            'Monday': [
                (datetime.time(11, 0), datetime.time(11, 30)),
                (datetime.time(14, 0), datetime.time(14, 30)),
                (datetime.time(15, 30), datetime.time(16, 0))
            ],
            'Tuesday': [
                (datetime.time(10, 30), datetime.time(11, 0)),
                (datetime.time(15, 0), datetime.time(15, 30))
            ],
            'Wednesday': [
                (datetime.time(10, 0), datetime.time(11, 0)),
                (datetime.time(11, 30), datetime.time(12, 0)),
                (datetime.time(12, 30), datetime.time(13, 0)),
                (datetime.time(13, 30), datetime.time(14, 0)),
                (datetime.time(15, 0), datetime.time(15, 30)),
                (datetime.time(16, 0), datetime.time(16, 30))
            ]
        }
        
        # Check if overlaps with any busy period
        for busy_start, busy_end in robert_busy[day]:
            if not (end_time <= busy_start or start_time >= busy_end):
                return False
        
        # Check if within work hours (9:00-17:00)
        if start_time < datetime.time(9, 0) or end_time > datetime.time(17, 0):
            return False
            
        return True
    
    # Ralph's constraints
    def ralph_available(day, start_hour, start_minute):
        start_time = datetime.time(start_hour, start_minute)
        end_time_minutes = start_hour * 60 + start_minute + 30
        end_hour = end_time_minutes // 60
        end_minute = end_time_minutes % 60
        end_time = datetime.time(end_hour, end_minute)
        
        # Ralph's busy times
        ralph_busy = {
            'Monday': [
                (datetime.time(10, 0), datetime.time(13, 30)),
                (datetime.time(14, 0), datetime.time(14, 30)),
                (datetime.time(15, 0), datetime.time(17, 0))
            ],
            'Tuesday': [
                (datetime.time(9, 0), datetime.time(9, 30)),
                (datetime.time(10, 0), datetime.time(10, 30)),
                (datetime.time(11, 0), datetime.time(11, 30)),
                (datetime.time(12, 0), datetime.time(13, 0)),
                (datetime.time(14, 0), datetime.time(15, 30)),
                (datetime.time(16, 0), datetime.time(17, 0))
            ],
            'Wednesday': [
                (datetime.time(10, 30), datetime.time(11, 0)),
                (datetime.time(11, 30), datetime.time(12, 0)),
                (datetime.time(13, 0), datetime.time(14, 30)),
                (datetime.time(16, 30), datetime.time(17, 0))
            ]
        }
        
        # Check if overlaps with any busy period
        for busy_start, busy_end in ralph_busy[day]:
            if not (end_time <= busy_start or start_time >= busy_end):
                return False
        
        # Check if within work hours (9:00-17:00)
        if start_time < datetime.time(9, 0) or end_time > datetime.time(17, 0):
            return False
            
        return True
    
    # Add constraints for both participants
    problem.addConstraint(robert_available, ['day', 'start_hour', 'start_minute'])
    problem.addConstraint(ralph_available, ['day', 'start_hour', 'start_minute'])
    
    # Find earliest available time (prefer Tuesday/Wednesday over Monday)
    solutions = problem.getSolutions()
    
    if not solutions:
        print("No solution found")
        return
    
    # Sort solutions: prioritize Tuesday, then Wednesday, then Monday, then by time
    def solution_key(sol):
        day_priority = {'Tuesday': 0, 'Wednesday': 1, 'Monday': 2}
        time_value = sol['start_hour'] * 60 + sol['start_minute']
        return (day_priority[sol['day']], time_value)
    
    best_solution = min(solutions, key=solution_key)
    
    day = best_solution['day']
    start_hour = best_solution['start_hour']
    start_minute = best_solution['start_minute']
    
    end_time_minutes = start_hour * 60 + start_minute + 30
    end_hour = end_time_minutes // 60
    end_minute = end_time_minutes % 60
    
    # Format output
    start_str = f"{start_hour:02d}:{start_minute:02d}"
    end_str = f"{end_hour:02d}:{end_minute:02d}"
    
    print(f"{day}")
    print(f"{start_str}:{end_str}")

if __name__ == "__main__":
    main()