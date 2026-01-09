from constraint import Problem

def main():
    problem = Problem()
    
    days = ['Monday', 'Tuesday', 'Wednesday']
    time_slots = []
    
    # Generate all possible 30-minute slots between 9:00 and 17:00
    for hour in range(9, 17):
        for minute in [0, 30]:
            if hour == 16 and minute == 30:
                continue
            start_time = f"{hour:02d}:{minute:02d}"
            end_hour = hour if minute == 0 else hour + 1
            end_minute = 30 if minute == 0 else 0
            end_time = f"{end_hour:02d}:{end_minute:02d}"
            time_slots.append((start_time, end_time))
    
    # Add variables for day and time slot
    problem.addVariable('day', days)
    problem.addVariable('time_slot', time_slots)
    
    # Define constraints
    def susan_available(day, time_slot):
        start_time, _ = time_slot
        
        if day == 'Monday':
            blocked = ['12:30', '13:30']
            return start_time not in blocked
        elif day == 'Tuesday':
            blocked = ['11:30']
            return start_time not in blocked
        elif day == 'Wednesday':
            blocked = ['09:30', '14:00', '15:30']
            return start_time not in blocked
        return True
    
    def sandra_available(day, time_slot):
        start_time, _ = time_slot
        
        if day == 'Monday':
            # Sandra busy: 9:00-13:00, 14:00-15:00, 16:00-16:30
            busy_slots = []
            for hour in range(9, 13):
                for minute in [0, 30]:
                    if hour == 12 and minute == 30:
                        continue
                    busy_slots.append(f"{hour:02d}:{minute:02d}")
            for hour in range(14, 15):
                for minute in [0, 30]:
                    busy_slots.append(f"{hour:02d}:{minute:02d}")
            busy_slots.append('16:00')
            return start_time not in busy_slots
        elif day == 'Tuesday':
            # Sandra busy: 9:00-9:30, 10:30-12:00, 12:30-13:30, 14:00-14:30, 16:00-17:00
            busy_slots = ['09:00', '10:30', '11:00', '11:30', '12:30', '13:00', '14:00', '16:00', '16:30']
            return start_time not in busy_slots
        elif day == 'Wednesday':
            # Sandra busy: 9:00-11:30, 12:00-12:30, 13:00-17:00
            busy_slots = []
            for hour in range(9, 11):
                for minute in [0, 30]:
                    busy_slots.append(f"{hour:02d}:{minute:02d}")
            busy_slots.extend(['11:00', '12:00', '13:00', '13:30', '14:00', '14:30', '15:00', '15:30', '16:00', '16:30'])
            return start_time not in busy_slots
        return True
    
    def preference_constraint(day, time_slot):
        # Susan would rather not meet on Tuesday
        if day == 'Tuesday':
            return False
        return True
    
    def monday_after_1600_constraint(day, time_slot):
        start_time, _ = time_slot
        # Sandra cannot meet on Monday after 16:00
        if day == 'Monday' and start_time >= '16:00':
            return False
        return True
    
    problem.addConstraint(susan_available, ['day', 'time_slot'])
    problem.addConstraint(sandra_available, ['day', 'time_slot'])
    problem.addConstraint(preference_constraint, ['day', 'time_slot'])
    problem.addConstraint(monday_after_1600_constraint, ['day', 'time_slot'])
    
    # Find solution
    solutions = problem.getSolutions()
    
    if solutions:
        solution = solutions[0]
        day = solution['day']
        start_time, end_time = solution['time_slot']
        print(f"{day}:{start_time}:{end_time}")
    else:
        print("No suitable time found")

if __name__ == "__main__":
    main()