# Define the workday start and end times
workday_start = 9 * 60  # 9:00 AM in minutes since midnight
workday_end = 17 * 60   # 5:00 PM in minutes since midnight

# Function to parse time strings into minutes since midnight
def parse_time(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

# Function to generate all possible 30-minute slots in the workday
def generate_slots():
    slots = set()
    current_time = workday_start
    while current_time < workday_end - 30:
        slots.add((current_time, current_time + 30))
        current_time += 30
    return slots

# Function to convert minutes since midnight back to HH:MM format
def format_time(minutes):
    hours = minutes // 60
    minutes = minutes % 60
    return f"{hours:02}:{minutes:02}"

# Blocked times for each participant
blocked_times = {
    'Judy': [(parse_time('13:00'), parse_time('13:30')), (parse_time('16:00'), parse_time('16:30'))],
    'Olivia': [(parse_time('10:00'), parse_time('10:30')), (parse_time('12:00'), parse_time('13:00')), (parse_time('14:00'), parse_time('14:30'))],
    'Eric': [],
    'Jacqueline': [(parse_time('10:00'), parse_time('10:30')), (parse_time('15:00'), parse_time('15:30'))],
    'Laura': [(parse_time('9:00'), parse_time('10:00')), (parse_time('10:30'), parse_time('12:00')),
              (parse_time('13:00'), parse_time('13:30')), (parse_time('14:30'), parse_time('15:00')),
              (parse_time('15:30'), parse_time('17:00'))],
    'Tyler': [(parse_time('9:00'), parse_time('10:00')), (parse_time('11:00'), parse_time('11:30')),
              (parse_time('12:30'), parse_time('13:00')), (parse_time('14:00'), parse_time('14:30')),
              (parse_time('15:30'), parse_time('17:00'))],
    'Lisa': [(parse_time('9:30'), parse_time('10:30')), (parse_time('11:00'), parse_time('11:30')),
             (parse_time('12:00'), parse_time('12:30')), (parse_time('13:00'), parse_time('13:30')),
             (parse_time('14:00'), parse_time('14:30')), (parse_time('16:00'), parse_time('17:00'))]
}

# Generate all possible slots
all_slots = generate_slots()

# Remove blocked slots for each participant
available_slots = all_slots.copy()
for participant, blocks in blocked_times.items():
    for block in blocks:
        for slot in all_slots:
            if block[0] <= slot[0] < block[1] or block[0] < slot[1] <= block[1]:
                available_slots.discard(slot)

# Find an available slot
if available_slots:
    slot = next(iter(available_slots))
    start_time_formatted = format_time(slot[0])
    end_time_formatted = format_time(slot[1])
    print(f"{start_time_formatted}:{end_time_formatted} Monday")
else:
    print("No available slot found, but the problem guarantees a solution.")