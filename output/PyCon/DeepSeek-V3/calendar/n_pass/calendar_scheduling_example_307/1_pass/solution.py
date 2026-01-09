from constraint import Problem
import datetime

def main():
    problem = Problem()
    
    # Define work hours
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    
    # Convert blocked times to minutes since midnight
    blocked_times = {
        'Ronald': [],
        'Stephen': [(10*60, 10*60+30), (12*60, 12*60+30)],
        'Brittany': [(11*60, 11*60+30), (13*60+30, 14*60), (15*60+30, 16*60), (16*60+30, 17*60)],
        'Dorothy': [(9*60, 9*60+30), (10*60, 10*60+30), (11*60, 12*60+30), (13*60, 15*60), (15*60+30, 17*60)],
        'Rebecca': [(9*60+30, 10*60+30), (11*60, 11*60+30), (12*60, 12*60+30), (13*60, 17*60)],
        'Jordan': [(9*60, 9*60+30), (10*60, 11*60), (11*60+30, 12*60), (13*60, 15*60), (15*60+30, 16*60+30)]
    }
    
    # Meeting duration in minutes
    meeting_duration = 30
    
    # Define possible start times (every 15 minutes for efficiency)
    possible_starts = list(range(work_start, work_end - meeting_duration + 1, 15))
    
    # Add variable for meeting start time
    problem.addVariable('meeting_start', possible_starts)
    
    # Add constraint for each participant
    for participant, blocked in blocked_times.items():
        def no_overlap_constraint(start, person=participant, blocked_slots=blocked, duration=meeting_duration):
            meeting_end = start + duration
            for block_start, block_end in blocked_slots:
                # Check if meeting overlaps with any blocked time
                if not (meeting_end <= block_start or start >= block_end):
                    return False
            return True
        
        problem.addConstraint(no_overlap_constraint, ['meeting_start'])
    
    # Find solution
    solutions = problem.getSolutions()
    
    if solutions:
        # Take the first solution
        meeting_start_minutes = solutions[0]['meeting_start']
        meeting_end_minutes = meeting_start_minutes + meeting_duration
        
        # Convert to time format
        start_hour = meeting_start_minutes // 60
        start_minute = meeting_start_minutes % 60
        end_hour = meeting_end_minutes // 60
        end_minute = meeting_end_minutes % 60
        
        # Format output
        time_range = f"{start_hour:02d}:{start_minute:02d}-{end_hour:02d}:{end_minute:02d}"
        print(f"Monday {time_range}")
    else:
        print("No suitable time found")

if __name__ == "__main__":
    main()