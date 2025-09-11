def main():
    # Given constraints and schedules
    days = ["Monday", "Tuesday", "Wednesday", "Thursday"]
    meeting_duration = 30  # minutes
    
    # Ruth's busy slots on Thursday (only available day)
    ruth_busy_thursday = [
        ("09:00", "11:00"),
        ("11:30", "14:30"),
        ("15:00", "17:00")
    ]
    
    # Convert time strings to minutes for easier calculation
    def time_to_minutes(time_str):
        h, m = map(int, time_str.split(':'))
        return h * 60 + m
    
    # Convert minutes back to HH:MM format
    def minutes_to_time(minutes):
        h = minutes // 60
        m = minutes % 60
        return f"{h:02d}:{m:02d}"
    
    # Generate free slots for Ruth on Thursday within work hours (9:00-17:00)
    work_start = time_to_minutes("09:00")
    work_end = time_to_minutes("17:00")
    ruth_free_slots = []
    
    # Check before first meeting
    if ruth_busy_thursday[0][0] != "09:00":
        ruth_free_slots.append(("09:00", ruth_busy_thursday[0][0]))
    
    # Check between meetings
    for i in range(len(ruth_busy_thursday) - 1):
        end_current = ruth_busy_thursday[i][1]
        start_next = ruth_busy_thursday[i+1][0]
        if end_current != start_next:
            ruth_free_slots.append((end_current, start_next))
    
    # Check after last meeting
    if ruth_busy_thursday[-1][1] != "17:00":
        ruth_free_slots.append((ruth_busy_thursday[-1][1], "17:00"))
    
    # Filter slots that are at least 30 minutes and avoid Julie's preference (before 11:30 on Thursday)
    suitable_slots = []
    for slot in ruth_free_slots:
        start_min = time_to_minutes(slot[0])
        end_min = time_to_minutes(slot[1])
        if end_min - start_min >= meeting_duration:
            # Check if slot starts before 11:30 (Julie's preference to avoid)
            if start_min >= time_to_minutes("11:30"):
                suitable_slots.append(slot)
    
    # Since there's exactly one suitable slot that meets all constraints
    chosen_slot = suitable_slots[0]
    start_time = chosen_slot[0]
    end_time = minutes_to_time(time_to_minutes(start_time) + meeting_duration)
    
    # Output the result
    print("Thursday")
    print(f"{start_time}:{end_time}")

if __name__ == "__main__":
    main()