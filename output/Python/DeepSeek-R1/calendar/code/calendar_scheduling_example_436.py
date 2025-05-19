def convert_time(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes - 9 * 60  # Convert to minutes since 09:00

def main():
    participants = {
        "Patrick": [("13:30", "14:00"), ("14:30", "15:00")],
        "Shirley": [("09:00", "09:30"), ("11:00", "11:30"), ("12:00", "12:30"), ("14:30", "15:00"), ("16:00", "17:00")],
        "Jeffrey": [("09:00", "09:30"), ("10:30", "11:00"), ("11:30", "12:00"), ("13:00", "13:30"), ("16:00", "17:00")],
        "Gloria": [("11:30", "12:00"), ("15:00", "15:30")],
        "Nathan": [("09:00", "09:30"), ("10:30", "12:00"), ("14:00", "17:00")],
        "Angela": [("09:00", "09:30"), ("10:00", "11:00"), ("12:30", "15:00"), ("15:30", "16:30")],
        "David": [("09:00", "09:30"), ("10:00", "10:30"), ("11:00", "14:00"), ("14:30", "16:30")]
    }

    # Convert all time slots to minutes since 09:00
    busy_slots = {}
    for person, slots in participants.items():
        busy_slots[person] = []
        for start, end in slots:
            start_min = convert_time(start)
            end_min = convert_time(end)
            busy_slots[person].append((start_min, end_min))

    # Check every 30-minute slot from 09:00 to 16:30
    for start_min in range(0, 480 - 30 + 1, 1):
        end_min = start_min + 30
        all_free = True
        for person, slots in busy_slots.items():
            conflict = any(s < end_min and e > start_min for (s, e) in slots)
            if conflict:
                all_free = False
                break
        if all_free:
            # Convert back to HH:MM format
            total_min = start_min + 9 * 60
            start_h = total_min // 60
            start_m = total_min % 60
            end_total_min = end_min + 9 * 60
            end_h = end_total_min // 60
            end_m = end_total_min % 60
            print(f"{start_h:02d}:{start_m:02d}:{end_h:02d}:{end_m:02d}")
            print("Monday")
            return

if __name__ == "__main__":
    main()