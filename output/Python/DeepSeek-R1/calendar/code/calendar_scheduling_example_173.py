def time_to_min(t):
    hours, minutes = map(int, t.split(':'))
    return hours * 60 + minutes

def min_to_time(m):
    return f"{m // 60:02d}:{m % 60:02d}"

participants = {
    "Jacqueline": {
        "busy": [
            ("9:00", "9:30"),
            ("11:00", "11:30"),
            ("12:30", "13:00"),
            ("15:30", "16:00")
        ]
    },
    "Harold": {
        "busy": [
            ("10:00", "10:30"),
            ("13:00", "13:30"),
            ("15:00", "17:00")
        ],
        "constraint": lambda start, end: end <= time_to_min("13:00")
    },
    "Arthur": {
        "busy": [
            ("9:00", "9:30"),
            ("10:00", "12:30"),
            ("14:30", "15:00"),
            ("15:30", "17:00")
        ]
    },
    "Kelly": {
        "busy": [
            ("9:00", "9:30"),
            ("10:00", "11:00"),
            ("11:30", "12:30"),
            ("14:00", "15:00"),
            ("15:30", "16:00")
        ]
    }
}

# Convert busy times to minutes
for person in participants.values():
    person["busy"] = [(time_to_min(s), time_to_min(e)) for s, e in person["busy"]]

# Check time slots from 9:00 to 12:30 (last possible start time to finish by 13:00)
for start_min in range(time_to_min("9:00"), time_to_min("12:30") + 1, 30):
    end_min = start_min + 30
    valid = True
    
    for person_name, data in participants.items():
        # Check Harold's time constraint
        if person_name == "Harold" and not data["constraint"](start_min, end_min):
            valid = False
            break
        
        # Check busy periods
        for busy_start, busy_end in data["busy"]:
            if busy_start < end_min and busy_end > start_min:
                valid = False
                break
        if not valid:
            break
    
    if valid:
        start_time = min_to_time(start_min)
        end_time = min_to_time(end_min)
        print(f"Monday:{start_time}:{end_time}")
        exit()

# If no slot found (though problem states there is a solution)
print("No valid time found")