from constraint import Problem, AllDifferentConstraint
import datetime

def create_time_slots(start_hour, end_hour, duration_minutes=30):
    """Create time slots of given duration between start and end hours"""
    slots = []
    current_time = datetime.datetime(2023, 1, 1, start_hour, 0)
    end_time = datetime.datetime(2023, 1, 1, end_hour, 0)
    
    while current_time + datetime.timedelta(minutes=duration_minutes) <= end_time:
        end_slot = current_time + datetime.timedelta(minutes=duration_minutes)
        slots.append((
            current_time.strftime("%H:%M"),
            end_slot.strftime("%H:%M")
        ))
        current_time += datetime.timedelta(minutes=30)
    
    return slots

def main():
    # Define the problem
    problem = Problem()
    
    # Create time slots from 9:00 to 17:00 in 30-minute intervals
    time_slots = create_time_slots(9, 17, 30)
    
    # Add variable for the meeting time slot
    problem.addVariable("meeting_time", range(len(time_slots)))
    
    # Define busy times for each person (slot indices where they are busy)
    # John: 11:30-12:00, 14:00-14:30
    john_busy = [5, 10, 11]  # 11:30-12:00, 14:00-14:30
    
    # Megan: 12:00-12:30, 14:00-15:00, 15:30-16:00
    megan_busy = [6, 10, 11, 12, 13, 15]  # 12:00-12:30, 14:00-15:00, 15:30-16:00
    
    # Brandon: no meetings (empty list)
    brandon_busy = []
    
    # Kimberly: 9:00-9:30, 10:00-10:30, 11:00-14:30, 15:00-16:00, 16:30-17:00
    kimberly_busy = [0, 2, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 15, 16]  # 9:00-9:30, 10:00-10:30, 11:00-14:30, 15:00-16:00, 16:30-17:00
    
    # Sean: 10:00-11:00, 11:30-14:00, 15:00-15:30
    sean_busy = [2, 3, 5, 6, 7, 8, 9, 12]  # 10:00-11:00, 11:30-14:00, 15:00-15:30
    
    # Lori: 9:00-9:30, 10:30-12:00, 13:00-14:30, 16:00-16:30
    lori_busy = [0, 3, 4, 5, 6, 8, 9, 10, 11, 14]  # 9:00-9:30, 10:30-12:00, 13:00-14:30, 16:00-16:30
    
    # Add constraints - meeting time cannot be in anyone's busy slots
    def not_in_john_busy(meeting_time):
        return meeting_time not in john_busy
    
    def not_in_megan_busy(meeting_time):
        return meeting_time not in megan_busy
    
    def not_in_kimberly_busy(meeting_time):
        return meeting_time not in kimberly_busy
    
    def not_in_sean_busy(meeting_time):
        return meeting_time not in sean_busy
    
    def not_in_lori_busy(meeting_time):
        return meeting_time not in lori_busy
    
    problem.addConstraint(not_in_john_busy, ["meeting_time"])
    problem.addConstraint(not_in_megan_busy, ["meeting_time"])
    problem.addConstraint(not_in_kimberly_busy, ["meeting_time"])
    problem.addConstraint(not_in_sean_busy, ["meeting_time"])
    problem.addConstraint(not_in_lori_busy, ["meeting_time"])
    
    # Find solutions
    solutions = problem.getSolutions()
    
    if solutions:
        # Get the first solution
        meeting_slot_idx = solutions[0]["meeting_time"]
        start_time, end_time = time_slots[meeting_slot_idx]
        
        print(f"Monday:{start_time}:{end_time}")
    else:
        print("No suitable time found")

if __name__ == "__main__":
    main()