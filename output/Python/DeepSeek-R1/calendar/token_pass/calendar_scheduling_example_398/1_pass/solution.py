def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    hours = minutes // 60
    minutes = minutes % 60
    return f"{hours:02d}:{minutes:02d}"

def main():
    participants = {
        'Doris': ['9:00-11:00', '13:30-14:00', '16:00-16:30'],
        'Theresa': ['10:00-12:00'],
        'Christian': [],
        'Terry': ['9:30-10:00', '11:30-12:00', '12:30-13:00', '13:30-14:00', '14:30-15:00', '15:30-17:00'],
        'Carolyn': ['9:00-10:30', '11:00-11:30', '12:00-13:00', '13:30-14:30', '15:00-17:00'],
        'Kyle': ['9:00-9:30', '11:30-12:00', '12:30-13:00', '14:30-17:00']
    }
    
    day_start = time_to_minutes('9:00')
    day_end = time_to_minutes('17:00')
    meeting_duration = 30
    
    all_busy = []
    for person, intervals in participants.items():
        for interval in intervals:
            start_str, end_str = interval.split('-')
            start_min = time_to_minutes(start_str)
            end_min = time_to_minutes(end_str)
            all_busy.append((start_min, end_min))
    
    if not all_busy:
        print("Monday 09:00:09:30")
        return
        
    all_busy.sort(key=lambda x: x[0])
    merged_busy = []
    current_start, current_end = all_busy[0]
    for start, end in all_busy[1:]:
        if start <= current_end:
            if end > current_end:
                current_end = end
        else:
            merged_busy.append((current_start, current_end))
            current_start, current_end = start, end
    merged_busy.append((current_start, current_end))
    
    free_slots = []
    previous_end = day_start
    for start, end in merged_busy:
        if start > previous_end:
            free_slots.append((previous_end, start))
        previous_end = max(previous_end, end)
    if previous_end < day_end:
        free_slots.append((previous_end, day_end))
    
    for slot_start, slot_end in free_slots:
        if slot_end - slot_start >= meeting_duration:
            meeting_start = slot_start
            meeting_end = meeting_start + meeting_duration
            start_time_str = minutes_to_time(meeting_start)
            end_time_str = minutes_to_time(meeting_end)
            print(f"Monday {start_time_str}:{end_time_str}")
            return
            
    print("No suitable time found")

if __name__ == "__main__":
    main()