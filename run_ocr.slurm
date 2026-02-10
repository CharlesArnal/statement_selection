#!/bin/bash
###############################################################################
# Slurm job array: OCR all 69 MIT course directories
#
# Before submitting, edit the #SBATCH directives and variables below.
#
# Usage:
#   Dry-run:       sbatch --test-only run_ocr.slurm
#   Single course: sbatch --array=0 run_ocr.slurm
#   Full launch:   sbatch run_ocr.slurm
#   Monitor:       squeue -u $USER && ls logs/
###############################################################################

#SBATCH --job-name=ocr_mit
#SBATCH --partition=scavenge
#SBATCH --gres=gpu:8
#SBATCH --time=8:00:00
#SBATCH --mem=32G
#SBATCH --array=0-68
#SBATCH --output=/checkpoint/%u/mit_ocr/%A_%a.out
#SBATCH --error=/checkpoint/%u/mit_ocr/%A_%a.err

# ─── User-configurable variables ────────────────────────────────────────────
CONDA_ENV="ocr"                              # conda environment name
PROJECT_DIR="/home/user/statement_selection"  # project path on cluster
# ────────────────────────────────────────────────────────────────────────────

set -euo pipefail

cd "${PROJECT_DIR}"
mkdir -p logs

# Activate conda
source "$(conda info --base)/etc/profile.d/conda.sh"
conda activate "${CONDA_ENV}"

# ─── Map task ID to course directory ────────────────────────────────────────
COURSES=($(ls -d mit_books/*/ | sort))

if [[ ${SLURM_ARRAY_TASK_ID} -ge ${#COURSES[@]} ]]; then
    echo "ERROR: SLURM_ARRAY_TASK_ID=${SLURM_ARRAY_TASK_ID} exceeds number of courses (${#COURSES[@]})"
    exit 1
fi

COURSE_DIR="${COURSES[${SLURM_ARRAY_TASK_ID}]}"
COURSE_NAME=$(basename "${COURSE_DIR}")

# ─── Run OCR ────────────────────────────────────────────────────────────────
echo "============================================"
echo "Job ${SLURM_ARRAY_JOB_ID}_${SLURM_ARRAY_TASK_ID}"
echo "Course: ${COURSE_NAME}"
echo "Directory: ${COURSE_DIR}"
echo "Node: $(hostname)"
echo "GPU: $(nvidia-smi --query-gpu=name --format=csv,noheader 2>/dev/null || echo 'N/A')"
echo "Start: $(date)"
echo "============================================"

python extract_pdf.py "${COURSE_DIR}" \
    --force-ocr \
    --use-llm \
    --llm-service openai \
    --merge-parts \
    --verbose

echo "============================================"
echo "Finished: ${COURSE_NAME}"
echo "End: $(date)"
echo "============================================"
