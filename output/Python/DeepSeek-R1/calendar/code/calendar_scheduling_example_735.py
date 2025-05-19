def time_to_minutes(t):
    h, m = map(int, t.split(':'))
    return h * 60 + m

def minutes_to_time(m):
    return f"{m // 60:02d}:{m % 60:02d}"

def is_available(person, day, start, end):
    for block in person['busy'][day]:
        block_start = time_to_minutes(block[0])
        block_end = time_to_minutes(block[1])
        if start < block_end and end > block_start:
            return False
    return True

ronald = {
    'busy': {
        'Monday': [('10:30', '11:00'), ('12:00', '12:30'), ('15:30', '16:00')],
        'Tuesday': [('9:00', '9:30'), ('12:00', '12:30'), ('15:30', '16:30')],
        'Wednesday': [('9:30', '10:30'), ('11:00', '12:00'), ('12:30', '13:00'), ('13:30', '14:00'), ('16:30', '17:00')]
    }
}

amber = {
    'busy': {
        'Monday': [('9:00', '9:30'), ('10:00', '10:30'), ('11:30', '12:00'), ('12:30', '14:00'), ('14:30', '15:00'), ('15:30', '17:00')],
        'Tuesday': [('9:00', '9:30'), ('10:00', '11:30'), ('12:00', '12:30'), ('13:30', '15:30'), ('16:30', '17:00')],
        'Wednesday': [('9:00', '9:30'), ('10:00', '10:30'), ('11:00', '13:30'), ('15:00', '15:30')]
    }
}

days = ['Monday', 'Tuesday', 'Wednesday']
duration = 30

for day in days:
    time = 9 * 60  # Start at 9:00
    while time + duration <= 17 * 60:  # End by 17:00
        current_start = time
        current_end = time + duration
        if (is_available(ronald, day, current_start, current_end) and
            is_available(amber, day, current_start, current_end)):
            print(f"{day}:{minutes_to_time(current_start)}:{minutes_to_time(current_end)}")
            exit()
        time += 1  # Check every minute increment

print("No suitable time found.")