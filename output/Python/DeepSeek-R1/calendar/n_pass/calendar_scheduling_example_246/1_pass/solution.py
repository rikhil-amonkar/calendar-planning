def main():
    # Total slots from 9:00 to 17:00 (16 slots of 30 minutes)
    total_slots = 16
    busy = [False] * total_slots  # False indicates free slot

    # Function to convert time string to minutes from 9:00
    def time_to_minutes(time_str):
        parts = time_str.split(':')
        hour = int(parts[0])
        minute = int(parts[1])
        return (hour - 9) * 60 + minute

    # Participants and their busy intervals
    participants = {
        "Jacob": ["13:30 to 14:00", "14:30 to 15:00"],
        "Diana": ["9:30 to 10:00", "11:30 to 12:00", "13:00 to 13:30", "16:00 to 16:30"],
        "Adam": ["9:30 to 10:30", "11:00 to 12:30", "15:30 to 16:00"],
        "Angela": ["9:30 to 10:00", "10:30 to 12:00", "13:00 to 15:30", "16:00 to 16:30"],
        "Dennis": ["9:00 to 9:30", "10:30 to 11:30", "13:00 to 15:00", "16:30 to 17:00"]
    }

    # Process each participant's intervals
    for intervals in participants.values():
        for interval in intervals:
            start_str, end_str = interval.split(' to ')
            start_minutes = time_to_minutes(start_str)
            end_minutes = time_to_minutes(end_str)
            start_slot = start_minutes // 30
            end_slot = end_minutes // 30  # exclusive end
            for slot in range(start_slot, end_slot):
                if slot < total_slots:
                    busy[slot] = True

    # Find the first free slot
    slot_index = None
    for i in range(total_slots):
        if not busy[i]:
            slot_index = i
            break

    # Convert slot index to time
    total_minutes_start = slot_index * 30
    total_minutes_end = total_minutes_start + 30
    start_hour = 9 + total_minutes_start // 60
    start_minute = total_minutes_start % 60
    end_hour = 9 + total_minutes_end // 60
    end_minute = total_minutes_end % 60

    # Format and output
    print("Monday")
    print(f"{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}")

if __name__ == "__main__":
    main()