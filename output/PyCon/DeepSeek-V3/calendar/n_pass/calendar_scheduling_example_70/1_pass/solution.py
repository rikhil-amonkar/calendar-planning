from constraint import Problem
import datetime

def schedule_meeting():
    problem = Problem()
    
    # Define work hours (9:00 to 17:00)
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    meeting_duration = 30  # minutes
    
    # Convert schedules to minutes from midnight
    # Denise: busy 12:00-12:30, 15:30-16:00
    denise_busy = [(12*60, 12*60+30), (15*60+30, 16*60)]
    
    # Angela: no meetings
    angela_busy = []
    
    # Natalie: busy 9:00-11:30, 12:00-13:00, 14:00-14:30, 15:00-17:00
    natalie_busy = [(9*60, 11*60+30), (12*60, 13*60), (14*60, 14*60+30), (15*60, 17*60)]
    
    # Create time slots (every 15 minutes for efficiency)
    time_slots = []
    for start_minute in range(work_start, work_end - meeting_duration + 1, 15):
        end_minute = start_minute + meeting_duration
        time_slots.append((start_minute, end_minute))
    
    # Add variable for time slot index
    problem.addVariable('time_slot', range(len(time_slots)))
    
    # Define constraint function
    def is_time_available(time_slot_idx):
        start, end = time_slots[time_slot_idx]
        
        # Check Denise's availability
        for busy_start, busy_end in denise_busy:
            if not (end <= busy_start or start >= busy_end):
                return False
        
        # Check Angela's availability (always available)
        # No need to check as she has no meetings
        
        # Check Natalie's availability
        for busy_start, busy_end in natalie_busy:
            if not (end <= busy_start or start >= busy_end):
                return False
        
        return True
    
    problem.addConstraint(is_time_available, ['time_slot'])
    
    # Find earliest solution
    solutions = problem.getSolutions()
    
    if not solutions:
        return None
    
    # Find earliest time slot
    earliest_slot = min(solutions, key=lambda x: x['time_slot'])
    start_minute, end_minute = time_slots[earliest_slot['time_slot']]
    
    # Convert minutes back to time format
    def minutes_to_time(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours:02d}:{mins:02d}"
    
    start_time = minutes_to_time(start_minute)
    end_time = minutes_to_time(end_minute)
    
    return start_time, end_time

def main():
    result = schedule_meeting()
    if result:
        start_time, end_time = result
        print(f"Monday:{start_time}:{end_time}")
    else:
        print("No available time slot found")

if __name__ == "__main__":
    main()