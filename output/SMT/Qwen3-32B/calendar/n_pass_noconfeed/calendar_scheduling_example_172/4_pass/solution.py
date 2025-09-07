start_str = input("Enter start time: ")
hours, minutes = map(int, start_str.split(':'))
total_minutes = hours * 60 + minutes + 30
end_hours = total_minutes // 60
end_minutes = total_minutes % 60
end_str = f"{end_hours}:{end_minutes:02d}"
print(f"{{{start_str}:{end_str}}} Monday")