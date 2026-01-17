#!/usr/bin/env python3
"""
Dataset loader for Natural Plan dataset.
Provides utilities to load and access problems from the dataset.
"""

import json
from pathlib import Path
from typing import Dict, List, Optional, Literal

# Path to the Natural Plan dataset
DATA_PATH = Path("../data/meeting_planning_100.json")

TaskType = Literal["calendar", "meeting", "trip"]


class NaturalPlanDataset:
    """Loader for the Natural Plan dataset."""
    
    def __init__(self):
        """Initialize the dataset loader."""
        self.data_path = DATA_PATH
        self._cache = {}
    
    def load_task_data(self, task_type: TaskType, split: str = "train") -> List[Dict]:
        """
        Load data for a specific task type and split.
        
        Args:
            task_type: Type of task ("calendar", "meeting", or "trip")
            split: Data split ("train" or "test")
        
        Returns:
            List of problem dictionaries
        """
        cache_key = f"{task_type}_{split}"
        
        if cache_key in self._cache:
            return self._cache[cache_key]
        
        file_path = self.data_path / f"{task_type}_{split}.json"
        
        if not file_path.exists():
            raise FileNotFoundError(f"Data file not found: {file_path}")
        
        with open(file_path, 'r') as f:
            data = json.load(f)
        
        self._cache[cache_key] = data
        return data
    
    def get_problem(self, task_type: TaskType, index: int, split: str = "train") -> Dict:
        """
        Get a specific problem by index.
        
        Args:
            task_type: Type of task
            index: Index of the problem
            split: Data split
        
        Returns:
            Problem dictionary
        """
        data = self.load_task_data(task_type, split)
        
        if index < 0 or index >= len(data):
            raise IndexError(f"Index {index} out of range (0-{len(data)-1})")
        
        return data[index]
    
    def get_problem_by_id(self, problem_id: str, task_type: Optional[TaskType] = None) -> Dict:
        """
        Get a problem by its ID.
        
        Args:
            problem_id: The problem ID
            task_type: Optional task type to narrow search
        
        Returns:
            Problem dictionary
        """
        task_types = [task_type] if task_type else ["calendar", "meeting", "trip"]
        
        for tt in task_types:
            for split in ["train", "test"]:
                try:
                    data = self.load_task_data(tt, split)
                    for problem in data:
                        if problem.get("id") == problem_id:
                            return problem
                except FileNotFoundError:
                    continue
        
        raise ValueError(f"Problem with ID '{problem_id}' not found")
    
    def count_problems(self, task_type: TaskType, split: str = "train") -> int:
        """Count number of problems in a task type and split."""
        data = self.load_task_data(task_type, split)
        return len(data)
    
    def get_random_problem(self, task_type: TaskType, split: str = "train", seed: Optional[int] = None) -> Dict:
        """
        Get a random problem from the dataset.
        
        Args:
            task_type: Type of task
            split: Data split
            seed: Random seed for reproducibility
        
        Returns:
            Random problem dictionary
        """
        import random
        if seed is not None:
            random.seed(seed)
        
        data = self.load_task_data(task_type, split)
        return random.choice(data)
    
    def format_problem(self, problem: Dict, shot_type: str = "0shot") -> str:
        """
        Format a problem for display or LLM input.
        
        Args:
            problem: Problem dictionary
            shot_type: "0shot" or "5shot" to select prompt type
        
        Returns:
            Formatted problem string
        """
        prompt_key = f"prompt_{shot_type}"
        
        if prompt_key not in problem:
            raise ValueError(f"Prompt type '{shot_type}' not found in problem")
        
        return problem[prompt_key]
    
    def get_golden_solution(self, problem: Dict) -> str:
        """
        Get the golden (correct) solution for a problem.
        
        Args:
            problem: Problem dictionary
        
        Returns:
            Golden solution string
        """
        return problem.get("golden_plan", "")
    
    def list_available_tasks(self) -> Dict[str, Dict[str, int]]:
        """
        List all available tasks and their counts.
        
        Returns:
            Dictionary with task types and split counts
        """
        result = {}
        
        for task_type in ["calendar", "meeting", "trip"]:
            result[task_type] = {}
            for split in ["train", "test"]:
                try:
                    count = self.count_problems(task_type, split)
                    result[task_type][split] = count
                except FileNotFoundError:
                    result[task_type][split] = 0
        
        return result


def main():
    """Demo usage of the dataset loader."""
    loader = NaturalPlanDataset()
    
    print("=== Natural Plan Dataset Loader ===\n")
    
    # List available tasks
    print("Available tasks:")
    tasks = loader.list_available_tasks()
    for task_type, splits in tasks.items():
        print(f"\n{task_type.upper()}:")
        for split, count in splits.items():
            print(f"  {split}: {count} problems")
    
    print("\n" + "="*50 + "\n")
    
    # Load and display a sample problem
    print("=== Sample Calendar Problem (0-shot) ===\n")
    problem = loader.get_problem("calendar", 0)
    print(f"ID: {problem['id']}")
    print(f"\nProblem:\n{loader.format_problem(problem, '0shot')}")
    print(f"\nGolden Solution:\n{loader.get_golden_solution(problem)}")
    
    print("\n" + "="*50 + "\n")
    
    # Show a meeting problem
    print("=== Sample Meeting Problem (0-shot) ===\n")
    problem = loader.get_problem("meeting", 0)
    print(f"ID: {problem['id']}")
    print(f"\nProblem:\n{loader.format_problem(problem, '0shot')}")
    print(f"\nGolden Solution:\n{loader.get_golden_solution(problem)}")


if __name__ == "__main__":
    main()

